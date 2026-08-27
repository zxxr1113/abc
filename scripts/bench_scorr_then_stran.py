#!/usr/bin/env python3
"""Compare &scorr with the extra optimization found by &stran.

For every input AIG, the worker performs exactly this pipeline:

    normalized input -> &scorr -> scorr.aig -> &stran -> final.aig -> dsec

&stran does not run a standalone global &scorr pass.  It uses scorr's
sequential correspondence engine only as the formal oracle for each proposed
transduction.  Therefore ``stran_extra_and_reduction`` measures the reduction
found after the baseline &scorr result.

Examples:
  python3 scripts/bench_scorr_then_stran.py \
      --aig-dir ~/benchmark/all_test/all --abc ~/abc/abc \
      --out scorr_then_stran.csv --jobs 64 --timeout 12800

  # Small Build pages with an easily edited proof budget.
  python3 scripts/bench_scorr_then_stran.py \
      --aig-dir benchmark --abc ./abc --jobs 4 --timeout 1800 \
      --stran-args '-P root -F 1 -C 1000 -S -1 -N 100 -B 64 -K 32 -Q 4 -W 8 -q 1 -w 8'
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import json
import os
import platform
import re
import resource
import shlex
import shutil
import socket
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, Tuple

from stran_profile import PROFILE_FIELDS, parse_experiment_profile


# Edit these defaults, or override them with --scorr-args / --stran-args.
DEFAULT_AIG_DIR = os.path.expanduser("~/benchmark/all_test/all/")
DEFAULT_ABC = os.path.expanduser("~/abc/abc")
DEFAULT_TIMEOUT = 12800
DEFAULT_JOBS = 64
DEFAULT_OUT = "scorr_then_stran.csv"
# Keep the baseline at the user's normal &scorr defaults.  Do not add -r:
# it toggles implication rings *off* because they are enabled by default.
DEFAULT_SCORR_ARGS = "-F 1 -C 200"
DEFAULT_STRAN_ARGS = (
    "-P root -F 1 -C 1000 -S -1 -N 100 -B 64 -K 32 "
    "-Q 4 -W 8 -q 1 -w 8 -p"
)
NA = "N/A"

STAGE_PROFILE_FIELDS = [
    "stage_and_before", "stage_and_after_comb", "stage_and_after_scorr",
    "comb_stage_and_gain", "seq_stage_and_gain",
    "stage_reg_before", "stage_reg_after_comb", "stage_reg_after_scorr",
    "comb_stage_reg_gain", "seq_stage_reg_gain",
]
for _stage in ("comb", "seq"):
    for _kind in ("constant", "existing", "constructed"):
        STAGE_PROFILE_FIELDS.extend([
            f"{_stage}_{_kind}_generated",
            f"{_stage}_{_kind}_submitted",
            f"{_stage}_{_kind}_selected",
            f"{_stage}_{_kind}_proved",
            f"{_stage}_{_kind}_and_gain",
            f"{_stage}_{_kind}_reg_gain",
        ])
    STAGE_PROFILE_FIELDS.extend([
        f"{_stage}_constructed_selected_gates",
        f"{_stage}_constructed_proved_gates",
        f"{_stage}_constructed_selected_max_gates",
        f"{_stage}_constructed_proved_max_gates",
        f"{_stage}_constant_ordered_and_gain",
        f"{_stage}_constant_ordered_reg_gain",
        f"{_stage}_existing_ordered_and_gain",
        f"{_stage}_existing_ordered_reg_gain",
        f"{_stage}_build_ordered_and_gain",
        f"{_stage}_build_ordered_reg_gain",
        f"{_stage}_build_only_and_gain",
        f"{_stage}_build_only_reg_gain",
        f"{_stage}_ordered_total_and_gain",
        f"{_stage}_ordered_total_reg_gain",
    ])


def run_abc(
    abc: str, command: str, timeout: int
) -> Tuple[str, str, int, int, int, int]:
    """Return stdout/stderr/status plus wall, child-user, and child-system ms."""
    started = time.perf_counter()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)

    def timing() -> tuple[int, int, int]:
        usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
        return (
            int((time.perf_counter() - started) * 1000),
            int((usage_after.ru_utime - usage_before.ru_utime) * 1000),
            int((usage_after.ru_stime - usage_before.ru_stime) * 1000),
        )

    try:
        result = subprocess.run(
            [abc, "-q", command], capture_output=True, text=True, timeout=timeout
        )
        elapsed, user_ms, system_ms = timing()
        return (result.stdout, result.stderr, result.returncode,
                elapsed, user_ms, system_ms)
    except subprocess.TimeoutExpired as exc:
        elapsed, user_ms, system_ms = timing()
        # Python >=3.13 returns bytes from TimeoutExpired.stdout even when
        # text=True was passed to run(); decode so callers only ever see str.
        stdout = exc.stdout
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        return stdout or "", "TIMEOUT", -1, elapsed, user_ms, system_ms
    except FileNotFoundError as exc:
        elapsed, user_ms, system_ms = timing()
        return "", str(exc), -2, elapsed, user_ms, system_ms


def aig_stats(path: Path) -> Tuple[Any, Any]:
    """Read AND and latch counts from a binary or ASCII AIGER header."""
    try:
        with path.open("rb") as handle:
            words = handle.readline().decode("ascii", errors="replace").split()
        if len(words) >= 6 and words[0] in {"aig", "aag"}:
            return int(words[5]), int(words[3])
    except (OSError, ValueError):
        pass
    return NA, NA


def status_from(rc: int, output_path: Path) -> str:
    if rc == -1:
        return "TIMEOUT"
    if rc == -2:
        return "ABC_NOT_FOUND"
    if rc != 0:
        return f"ABC_ERROR({rc})"
    if not output_path.is_file():
        return "NO_OUTPUT"
    return "PASS"


def subtract(left: Any, right: Any) -> Any:
    return left - right if isinstance(left, int) and isinstance(right, int) else NA


def profiled_args(arguments: str) -> str:
    """Force exactly one -p for comparable experiment records."""
    try:
        tokens = shlex.split(arguments)
    except ValueError as exc:
        raise ValueError(f"cannot parse &stran arguments: {exc}") from exc
    tokens = [token for token in tokens if token != "-p"]
    tokens.append("-p")
    return " ".join(tokens)


def profile_number(text: str) -> int | float:
    """Parse an integer or decimal profiler token without losing exact counts."""
    return float(text) if "." in text else int(text)


def parse_stran(stdout: str) -> Dict[str, Any]:
    lines = [line for line in stdout.splitlines() if "Sequential transduction:" in line]
    line = lines[-1] if lines else ""
    result: Dict[str, Any] = {}
    for key in (
        "victim-sets", "proofs", "sig-matched", "gain-positive", "gain-rejected",
        "retain-unproved", "final-unproved", "accepted",
    ):
        match = re.search(rf"{re.escape(key)}=(\d+)", line)
        result[key.replace("-", "_")] = int(match.group(1)) if match else NA

    # The legacy stage-kind line reports exact subset Shapley attribution.  It
    # remains available for backward compatibility, while the ordered line
    # below reports C, E-after-C, B-after-CE, and the Build-only counterfactual.
    stage_records: Dict[str, Tuple[float, Dict[str, Any]]] = {}
    for stage_line in (
        item for item in stdout.splitlines()
        if "Sequential direct stage-kind profile:" in item
    ):
        stage_match = re.search(r"(?:^| )stage=(comb|seq)(?: |$)", stage_line)
        if not stage_match:
            continue
        stage = stage_match.group(1)
        record: Dict[str, Any] = {}
        score = 0.0
        for kind in ("constant", "existing", "constructed"):
            match = re.search(
                rf"(?:^| ){kind}=(\d+)/(\d+) "
                rf"and-gain=(-?\d+(?:\.\d+)?) "
                rf"reg-gain=(-?\d+(?:\.\d+)?)",
                stage_line,
            )
            if not match:
                continue
            selected, proved = int(match.group(1)), int(match.group(2))
            and_gain = profile_number(match.group(3))
            reg_gain = profile_number(match.group(4))
            record[f"{stage}_{kind}_selected"] = selected
            record[f"{stage}_{kind}_proved"] = proved
            record[f"{stage}_{kind}_and_gain"] = and_gain
            record[f"{stage}_{kind}_reg_gain"] = reg_gain
            score += selected + proved + abs(float(and_gain)) + abs(float(reg_gain))
        gates = re.search(
            r"constructed-gates=(\d+)/(\d+) max-gates=(\d+)/(\d+)",
            stage_line,
        )
        if gates:
            record[f"{stage}_constructed_selected_gates"] = int(gates.group(1))
            record[f"{stage}_constructed_proved_gates"] = int(gates.group(2))
            record[f"{stage}_constructed_selected_max_gates"] = int(gates.group(3))
            record[f"{stage}_constructed_proved_max_gates"] = int(gates.group(4))
        sizes = re.search(
            r"; AND=(\d+) -> (\d+) gain=(-?\d+); "
            r"Reg=(\d+) -> (\d+) gain=(-?\d+)",
            stage_line,
        )
        if sizes:
            and_before, and_after, and_gain = map(int, sizes.group(1, 2, 3))
            reg_before, reg_after, reg_gain = map(int, sizes.group(4, 5, 6))
            record[f"{stage}_stage_and_gain"] = and_gain
            record[f"{stage}_stage_reg_gain"] = reg_gain
            if stage == "comb":
                record["stage_and_before"] = and_before
                record["stage_and_after_comb"] = and_after
                record["stage_reg_before"] = reg_before
                record["stage_reg_after_comb"] = reg_after
            else:
                record["stage_and_after_comb"] = and_before
                record["stage_and_after_scorr"] = and_after
                record["stage_reg_after_comb"] = reg_before
                record["stage_reg_after_scorr"] = reg_after
            score += abs(and_gain) + abs(reg_gain)
        if stage not in stage_records or score > stage_records[stage][0]:
            stage_records[stage] = (score, record)
    for _, record in stage_records.values():
        result.update(record)

    # Root-only schema 3/4 reports the 2x3 generated/submitted/proved/
    # selected matrix directly.  Build is named "constructed" in the existing
    # CSV columns to keep old analysis notebooks source-compatible.
    root_stage_gains = {"comb": [0, 0], "seq": [0, 0]}
    saw_root_effect = False
    for stage_line in (
        item for item in stdout.splitlines()
        if "stran-root experiment-effect profile:" in item
    ):
        stage_match = re.search(r"(?:^| )stage=(comb|seq)(?: |$)", stage_line)
        kind_match = re.search(
            r"(?:^| )kind=(constant|existing|build)(?: |$)", stage_line)
        if not stage_match or not kind_match:
            continue
        saw_root_effect = True
        stage = stage_match.group(1)
        kind = "constructed" if kind_match.group(1) == "build" else kind_match.group(1)
        for metric in ("generated", "submitted", "proved", "selected"):
            match = re.search(rf"(?:^| ){metric}=(-?\d+)(?: |$)", stage_line)
            if match:
                field = f"{stage}_{kind}_{metric}"
                result[field] = result.get(field, 0) + int(match.group(1))
        for index, (metric, suffix) in enumerate(
            (("marginal-and", "and_gain"), ("marginal-reg", "reg_gain"))
        ):
            match = re.search(rf"(?:^| ){metric}=(-?\d+)(?: |$)", stage_line)
            if match:
                value = int(match.group(1))
                field = f"{stage}_{kind}_{suffix}"
                result[field] = result.get(field, 0) + value
                root_stage_gains[stage][index] += value
    if saw_root_effect:
        for stage in ("comb", "seq"):
            result[f"{stage}_stage_and_gain"] = root_stage_gains[stage][0]
            result[f"{stage}_stage_reg_gain"] = root_stage_gains[stage][1]

    root_summaries = [
        item for item in stdout.splitlines()
        if "stran-root experiment-summary profile:" in item
    ]
    if root_summaries:
        def summary_int(line: str, key: str) -> int | None:
            match = re.search(rf"(?:^| ){key}=(-?\d+)(?: |$)", line)
            return int(match.group(1)) if match else None

        first_and = summary_int(root_summaries[0], "and-before")
        final_and = summary_int(root_summaries[-1], "and-after")
        first_reg = summary_int(root_summaries[0], "reg-before")
        final_reg = summary_int(root_summaries[-1], "reg-after")
        comb_summaries = [
            line for line in root_summaries
            if re.search(r"(?:^| )phase=comb(?: |$)", line)
        ]
        if first_and is not None and final_and is not None:
            result["stage_and_before"] = first_and
            result["stage_and_after_scorr"] = final_and
            if comb_summaries:
                after_comb = summary_int(comb_summaries[-1], "and-after")
                if after_comb is not None:
                    result["stage_and_after_comb"] = after_comb
                    result["comb_stage_and_gain"] = first_and - after_comb
                    result["seq_stage_and_gain"] = after_comb - final_and
            else:
                # Backward-compatible schema <=4 fallback.  These records did
                # not identify the chronological phase explicitly.
                result["stage_and_after_comb"] = (
                    first_and - root_stage_gains["comb"][0])
        if first_reg is not None and final_reg is not None:
            result["stage_reg_before"] = first_reg
            result["stage_reg_after_scorr"] = final_reg
            if comb_summaries:
                after_comb_reg = summary_int(comb_summaries[-1], "reg-after")
                if after_comb_reg is not None:
                    result["stage_reg_after_comb"] = after_comb_reg
                    result["comb_stage_reg_gain"] = first_reg - after_comb_reg
                    result["seq_stage_reg_gain"] = after_comb_reg - final_reg

    ordered_records: Dict[str, Tuple[float, Dict[str, Any]]] = {}
    for ordered_line in (
        item for item in stdout.splitlines()
        if "Sequential direct stage-kind ordered profile:" in item
    ):
        stage_match = re.search(r"(?:^| )stage=(comb|seq)(?: |$)", ordered_line)
        if not stage_match:
            continue
        stage = stage_match.group(1)
        record = {}
        score = 0.0
        for label in ("constant", "existing", "build", "build-only"):
            match = re.search(
                rf"(?:^| ){label}-and-gain=(-?\d+) reg-gain=(-?\d+)",
                ordered_line,
            )
            if not match:
                continue
            field = label.replace("-", "_")
            and_gain, reg_gain = int(match.group(1)), int(match.group(2))
            record[f"{stage}_{field}_ordered_and_gain" if label != "build-only"
                   else f"{stage}_build_only_and_gain"] = and_gain
            record[f"{stage}_{field}_ordered_reg_gain" if label != "build-only"
                   else f"{stage}_build_only_reg_gain"] = reg_gain
            score += abs(and_gain) + abs(reg_gain)
        total = re.search(
            r"; total-and-gain=(-?\d+) total-reg-gain=(-?\d+)", ordered_line)
        if total:
            record[f"{stage}_ordered_total_and_gain"] = int(total.group(1))
            record[f"{stage}_ordered_total_reg_gain"] = int(total.group(2))
            score += abs(int(total.group(1))) + abs(int(total.group(2)))
        if stage not in ordered_records or score > ordered_records[stage][0]:
            ordered_records[stage] = (score, record)
    for _, record in ordered_records.values():
        result.update(record)
    result.update(parse_experiment_profile(stdout))
    return result


def short_error(stdout: str, stderr: str) -> str:
    text = (stderr or stdout).strip().replace("\n", " | ")
    return text[:500] if text else NA


RUN_FIELDS = [
    "run_schema", "run_config_id", "run_started_at", "git_commit",
    "git_dirty", "abc_sha256", "script_sha256", "profile_parser_sha256",
    "host", "platform", "python_version", "aig_root", "timeout_s", "jobs",
    "dsec_mode", "input_count", "input_manifest_id", "input_sha256",
    "input_size_bytes",
    "normalize_user_ms", "normalize_system_ms", "scorr_user_ms",
    "scorr_system_ms", "stran_user_ms", "stran_system_ms", "dsec_user_ms",
    "dsec_system_ms",
]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def git_value(repo: Path, *args: str) -> str:
    try:
        result = subprocess.run(
            ["git", "-C", str(repo), *args], capture_output=True,
            text=True, timeout=10, check=False,
        )
        return result.stdout.strip() if result.returncode == 0 else NA
    except (OSError, subprocess.SubprocessError):
        return NA


def make_run_metadata(
    abc: Path, aig_dir: Path, timeout: int, jobs: int, skip_dsec: bool,
    scorr_args: str, stran_args: str, aigs: list[Path],
) -> dict[str, Any]:
    script = Path(__file__).resolve()
    parser_path = script.with_name("stran_profile.py")
    repo = script.parent.parent
    commit = git_value(repo, "rev-parse", "HEAD")
    dirty_text = git_value(repo, "status", "--porcelain", "--untracked-files=no")
    dirty = NA if dirty_text == NA else ("yes" if dirty_text else "no")
    manifest_rows = [
        f"{path.relative_to(aig_dir)}\t{path.stat().st_size}\t{sha256_file(path)}"
        for path in aigs
    ]
    manifest_id = hashlib.sha256("\n".join(manifest_rows).encode()).hexdigest()
    static = {
        "run_schema": 2,
        "git_commit": commit,
        "git_dirty": dirty,
        "abc_sha256": sha256_file(abc),
        "script_sha256": sha256_file(script),
        "profile_parser_sha256": sha256_file(parser_path),
        "host": socket.gethostname(),
        "platform": platform.platform(),
        "python_version": platform.python_version(),
        "aig_root": str(aig_dir),
        "timeout_s": timeout,
        "jobs": jobs,
        "dsec_mode": "skip" if skip_dsec else "audit",
        "input_count": len(aigs),
        "input_manifest_id": manifest_id,
        "scorr_args": scorr_args,
        "stran_args": stran_args,
    }
    encoded = json.dumps(static, sort_keys=True, separators=(",", ":")).encode()
    static["run_config_id"] = hashlib.sha256(encoded).hexdigest()[:20]
    static["run_started_at"] = dt.datetime.now(dt.timezone.utc).isoformat()
    return static


def worker(
    task: Tuple[str, str, str, str, int, str, bool, str, bool, dict[str, Any]]
) -> Dict[str, Any]:
    (aig_name, relative_name, abc, scorr_args, timeout, stran_args,
     keep_artifacts, artifacts_root, skip_dsec, run_metadata) = task
    source = Path(aig_name)
    row: Dict[str, Any] = {
        **run_metadata,
        "file": relative_name,
        "scorr_args": scorr_args,
        "stran_args": stran_args,
        "source_and": NA,
        "source_latches": NA,
        "scorr_status": NA,
        "stran_status": NA,
        "dsec_status": NA,
        "normalize_time_ms": NA,
        "scorr_time_ms": NA,
        "stran_time_ms": NA,
        "dsec_time_ms": NA,
        "total_time_ms": NA,
        "input_sha256": NA,
        "input_size_bytes": NA,
        "normalize_user_ms": NA,
        "normalize_system_ms": NA,
        "scorr_user_ms": NA,
        "scorr_system_ms": NA,
        "stran_user_ms": NA,
        "stran_system_ms": NA,
        "dsec_user_ms": NA,
        "dsec_system_ms": NA,
        "scorr_and": NA,
        "scorr_latches": NA,
        "stran_and": NA,
        "stran_latches": NA,
        "scorr_and_reduction": NA,
        "scorr_latch_reduction": NA,
        "stran_extra_and_reduction": NA,
        "stran_extra_latch_reduction": NA,
        "total_and_reduction": NA,
        "total_latch_reduction": NA,
        "victim_sets": NA,
        "proofs": NA,
        "sig_matched": NA,
        "gain_positive": NA,
        "gain_rejected": NA,
        "retain_unproved": NA,
        "final_unproved": NA,
        "accepted": NA,
        "error": NA,
    }
    row.update({field: NA for field in STAGE_PROFILE_FIELDS})
    row.update({field: NA for field in PROFILE_FIELDS if field not in STAGE_PROFILE_FIELDS})
    started = time.perf_counter()
    tag = hashlib.sha1(relative_name.encode("utf-8")).hexdigest()[:12]
    artifact_dir = Path(artifacts_root) / tag
    work_dir = artifact_dir if keep_artifacts else Path(tempfile.mkdtemp(prefix=f"scorr_stran_{tag}_"))
    if keep_artifacts:
        work_dir.mkdir(parents=True, exist_ok=True)
    norm_out = norm_err = scorr_out = scorr_err = stran_out = stran_err = dsec_out = dsec_err = ""

    try:
        row["input_sha256"] = sha256_file(source)
        row["input_size_bytes"] = source.stat().st_size
        # Rewriting the source once makes all AIGER names consistent.  dsec
        # then compares this normalized baseline with the final result.
        base = work_dir / "base.aig"
        scorr = work_dir / "scorr.aig"
        final = work_dir / "final.aig"
        norm_out, norm_err, norm_rc, norm_ms, norm_user, norm_system = run_abc(
            abc, f"&read {source}; &write {base}", timeout
        )
        row["normalize_time_ms"] = norm_ms
        row["normalize_user_ms"] = norm_user
        row["normalize_system_ms"] = norm_system
        norm_status = status_from(norm_rc, base)
        if norm_status != "PASS":
            row["error"] = f"normalize:{norm_status}: {short_error(norm_out, norm_err)}"
            return row
        # Measure the source from the normalized rewrite, not the raw AIGER
        # header: &read expands latch init values into init-mux AND gates, so
        # the raw header undercounts the ANDs that &scorr actually starts from.
        source_and, source_latches = aig_stats(base)
        row["source_and"] = source_and
        row["source_latches"] = source_latches

        scorr_out, scorr_err, scorr_rc, scorr_ms, scorr_user, scorr_system = run_abc(
            abc, f"&read {base}; &scorr {scorr_args}; &write {scorr}", timeout
        )
        row["scorr_time_ms"] = scorr_ms
        row["scorr_user_ms"] = scorr_user
        row["scorr_system_ms"] = scorr_system
        row["scorr_status"] = status_from(scorr_rc, scorr)
        if row["scorr_status"] != "PASS":
            row["error"] = f"scorr:{row['scorr_status']}: {short_error(scorr_out, scorr_err)}"
            return row
        row["scorr_and"], row["scorr_latches"] = aig_stats(scorr)
        row["scorr_and_reduction"] = subtract(source_and, row["scorr_and"])
        row["scorr_latch_reduction"] = subtract(source_latches, row["scorr_latches"])

        # This starts strictly from the completed &scorr output.  &stran's
        # own time includes its per-candidate sequential proof calls.
        stran_out, stran_err, stran_rc, stran_ms, stran_user, stran_system = run_abc(
            abc, f"&read {scorr}; &stran {stran_args}; &write {final}", timeout
        )
        row["stran_time_ms"] = stran_ms
        row["stran_user_ms"] = stran_user
        row["stran_system_ms"] = stran_system
        row["stran_status"] = status_from(stran_rc, final)
        row.update(parse_stran(stran_out))
        if row["stran_status"] != "PASS":
            row["error"] = f"stran:{row['stran_status']}: {short_error(stran_out, stran_err)}"
            return row
        row["stran_and"], row["stran_latches"] = aig_stats(final)
        row["stran_extra_and_reduction"] = subtract(row["scorr_and"], row["stran_and"])
        row["stran_extra_latch_reduction"] = subtract(row["scorr_latches"], row["stran_latches"])
        row["total_and_reduction"] = subtract(source_and, row["stran_and"])
        row["total_latch_reduction"] = subtract(source_latches, row["stran_latches"])

        if skip_dsec:
            row["dsec_status"] = "SKIP"
            row["dsec_time_ms"] = 0
        else:
            dsec_out, dsec_err, dsec_rc, dsec_ms, dsec_user, dsec_system = run_abc(
                abc, f"dsec {base} {final}", timeout
            )
            row["dsec_time_ms"] = dsec_ms
            row["dsec_user_ms"] = dsec_user
            row["dsec_system_ms"] = dsec_system
            row["dsec_status"] = (
                "PASS" if dsec_rc == 0 and "Networks are equivalent" in dsec_out
                else "TIMEOUT" if dsec_rc == -1
                else f"FAIL({dsec_rc})"
            )
            if row["dsec_status"] != "PASS":
                row["error"] = (
                    f"dsec:{row['dsec_status']}: "
                    f"{short_error(dsec_out, dsec_err)}"
                )

    finally:
        row["total_time_ms"] = int((time.perf_counter() - started) * 1000)
        if keep_artifacts:
            for name, content in (("normalize.log", norm_out + norm_err),
                                  ("scorr.log", scorr_out + scorr_err),
                                  ("stran.log", stran_out + stran_err),
                                  ("dsec.log", dsec_out + dsec_err)):
                (work_dir / name).write_text(content, encoding="utf-8")
        else:
            shutil.rmtree(work_dir, ignore_errors=True)

    return row


CSV_FIELDS = [
    *RUN_FIELDS,
    "file", "scorr_args", "stran_args",
    "source_and", "source_latches", "scorr_status", "stran_status", "dsec_status",
    "normalize_time_ms", "scorr_time_ms", "stran_time_ms", "dsec_time_ms", "total_time_ms",
    "scorr_and", "scorr_latches", "stran_and", "stran_latches",
    "scorr_and_reduction", "scorr_latch_reduction",
    "stran_extra_and_reduction", "stran_extra_latch_reduction",
    "total_and_reduction", "total_latch_reduction",
    *STAGE_PROFILE_FIELDS,
    *[field for field in PROFILE_FIELDS if field not in STAGE_PROFILE_FIELDS],
    "victim_sets", "proofs", "sig_matched", "gain_positive", "gain_rejected",
    "retain_unproved", "final_unproved", "accepted", "error",
]


def write_csv_atomic(output: Path, rows: list[Dict[str, Any]]) -> None:
    """Checkpoint completed cases without exposing a partially written CSV."""
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + ".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    os.replace(temporary, output)


def main() -> None:
    parser = argparse.ArgumentParser(description="Benchmark &scorr followed by &stran.")
    parser.add_argument("--aig-dir", default=DEFAULT_AIG_DIR)
    parser.add_argument("--abc", default=DEFAULT_ABC)
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT,
                        help="seconds per normalize/scorr/stran/dsec ABC invocation")
    parser.add_argument("--out", default=DEFAULT_OUT)
    parser.add_argument("--jobs", type=int, default=DEFAULT_JOBS)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--scorr-args", default=DEFAULT_SCORR_ARGS)
    parser.add_argument("--stran-args", default=DEFAULT_STRAN_ARGS)
    parser.add_argument("--keep-artifacts", action="store_true",
                        help="keep AIGs and logs next to the CSV, including failed cases")
    parser.add_argument(
        "--skip-dsec", action="store_true",
        help="skip the final equivalence audit and write dsec_status=SKIP",
    )
    args = parser.parse_args()

    try:
        stran_args = profiled_args(args.stran_args)
    except ValueError as exc:
        sys.exit(f"[ERROR] {exc}")

    aig_dir = Path(args.aig_dir).expanduser().resolve()
    abc_path = Path(args.abc).expanduser().resolve()
    abc = str(abc_path)
    output = Path(args.out).expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    if not aig_dir.is_dir():
        sys.exit(f"[ERROR] AIG directory not found: {aig_dir}")
    if not abc_path.is_file():
        sys.exit(f"[ERROR] ABC binary not found: {abc_path}")
    if args.timeout < 1 or args.jobs < 1:
        sys.exit("[ERROR] --timeout and --jobs must be positive")

    aigs = sorted(aig_dir.rglob("*.aig"))
    if args.limit is not None:
        aigs = aigs[:args.limit]
    if not aigs:
        sys.exit(f"[ERROR] No .aig files under {aig_dir}")

    print(f"[INFO] Pipeline: normalized input -> &scorr -> &stran -> dsec")
    print(f"[INFO] Files={len(aigs)} jobs={args.jobs} timeout={args.timeout}s")
    print(f"[INFO] &scorr args: {args.scorr_args}")
    print(f"[INFO] &stran args: {stran_args}")

    run_metadata = make_run_metadata(
        abc_path, aig_dir, args.timeout, args.jobs, args.skip_dsec,
        args.scorr_args, stran_args, aigs,
    )
    print(
        f"[INFO] Run config={run_metadata['run_config_id']} "
        f"commit={str(run_metadata['git_commit'])[:12]} "
        f"dirty={run_metadata['git_dirty']} host={run_metadata['host']}"
    )

    tasks = [
        (str(path), str(path.relative_to(aig_dir)), abc, args.scorr_args, args.timeout,
         stran_args, args.keep_artifacts,
         str(output.parent / f"{output.stem}_artifacts"), args.skip_dsec,
         run_metadata)
        for path in aigs
    ]
    rows = []
    started = time.perf_counter()

    def collect(name: str, future: Any, done: int) -> None:
        try:
            row = future() if callable(future) else future.result()
        except Exception as exc:  # Keep one bad benchmark from losing the CSV.
            row = {field: "ERROR" for field in CSV_FIELDS}
            row["file"] = name
            row["error"] = repr(exc)
        rows.append(row)
        write_csv_atomic(output, rows)
        print(
                f"[{done:>4}/{len(tasks)}] {name:45s} "
                f"scorr={row['scorr_time_ms']}ms stran={row['stran_time_ms']}ms "
                f"extraAND={row['stran_extra_and_reduction']} "
                f"extraLatch={row['stran_extra_latch_reduction']} dsec={row['dsec_status']}"
        )

    try:
        if args.jobs == 1:
            for done, task in enumerate(tasks, start=1):
                collect(task[1], lambda task=task: worker(task), done)
        else:
            pool = ProcessPoolExecutor(max_workers=args.jobs)
            futures = {pool.submit(worker, task): task[1] for task in tasks}
            try:
                for done, future in enumerate(as_completed(futures), start=1):
                    collect(futures[future], future, done)
            except KeyboardInterrupt:
                # Queued cases are cancelled.  The up-to-jobs active ABC
                # processes may finish, but their results are not needed for
                # the already checkpointed partial CSV.
                for future in futures:
                    future.cancel()
                try:
                    pool.shutdown(wait=False, cancel_futures=True)
                except TypeError:  # Python < 3.9
                    pool.shutdown(wait=False)
                raise
            else:
                pool.shutdown(wait=True)
    except KeyboardInterrupt:
        rows.sort(key=lambda row: row["file"])
        write_csv_atomic(output, rows)
        print(f"\n[STOP] Stopped by user. Partial CSV with {len(rows)} completed cases: {output}")
        return

    rows.sort(key=lambda row: row["file"])
    write_csv_atomic(output, rows)
    elapsed = time.perf_counter() - started
    print(f"[INFO] Done in {elapsed:.1f}s. CSV: {output}")


if __name__ == "__main__":
    main()
