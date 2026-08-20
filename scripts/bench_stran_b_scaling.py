#!/usr/bin/env python3
"""Sweep &stran's local divisor-pool limit (-B) on one AIG case.

The experiment keeps every other &stran parameter fixed, forces exhaustive
root search and profiling, and records the exact sequential Build contribution
and internal time shares in addition to candidate coverage and final size.

Example:
  python3 scripts/bench_stran_b_scaling.py \
      --aig path/to/sequential_case.aig --abc ./abc \
      --b-values 2,4,8,16,32,64,0 \
      --out results/stran_b_scaling/b_sweep.csv
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, Tuple

from stran_profile import PROFILE_FIELDS, parse_experiment_profile


NA = "N/A"
DEFAULT_B_VALUES = "2,4,8,16,32,64,0"
DEFAULT_STRAN_ARGS = (
    "-P root -F 1 -C 200 -S -1 -N 20 -K 32 -Q 4 -W 8 "
    "-q 1 -A 8 -L 32 -w 8"
)
RUN_SCHEMA_VERSION = "stran-b-scaling-v3-paged"

# The C profiler bins exact yields 0..63 and folds every larger dynamically
# enumerated result into y64.  Keep the full fixed profile to preserve root
# coverage while the candidate vector itself remains unbounded.
DEPENDENCY_YIELD_FIELDS = [f"dependency_yield_{count}" for count in range(65)]

METRIC_FIELDS = [
    "rounds", "roots", "proofs", "constructed", "sig_checks",
    "sig_rejected", "sig_matched", "accepted", "seq_scheduling",
    "root_snapshots", "root_closures", "root_batch_calls",
    "root_batch_candidates", "root_batch_proved", "root_batch_max",
    "root_screened", "construct_div_pool_calls", "construct_div_pool_nodes",
    "construct_dependency_calls", "construct_dependency_found",
    "construct_dependency_attempts", "construct_dependency_recipes",
    "comb_candidates", "comb_proved", "scorr_candidates", "scorr_seeded",
    "scorr_proved", *DEPENDENCY_YIELD_FIELDS,
    *PROFILE_FIELDS,
]

CSV_FIELDS = [
    "case", "b_value", "b_label", "run_schema", "run_started_at",
    "git_commit", "git_dirty", "abc_sha256", "script_sha256",
    "stran_args_base", "stran_args_effective", "timeout_s", "dsec_mode",
    "status", "dsec_status", "base_and", "final_and", "and_reduction",
    "and_reduction_pct", "base_latches", "final_latches", "latch_reduction",
    "time_ms", "dsec_time_ms", *METRIC_FIELDS,
    "candidate_exposure", "candidate_exposure_rel_pct", "sig_match_rate_pct",
    "proof_rate_pct", "accepted_rate_pct", "roots_with_candidate",
    "roots_searched_for_candidate", "root_coverage_pct",
    "root_build_search_pct", "error",
]


def as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def run_abc(abc: str, command: str, timeout: int) -> Tuple[str, str, int, int]:
    started = time.perf_counter()
    try:
        result = subprocess.run(
            [abc, "-q", command], capture_output=True, text=True, timeout=timeout
        )
        elapsed = int((time.perf_counter() - started) * 1000)
        return result.stdout, result.stderr, result.returncode, elapsed
    except subprocess.TimeoutExpired as exc:
        elapsed = int((time.perf_counter() - started) * 1000)
        return as_text(exc.stdout), as_text(exc.stderr) or "TIMEOUT", -1, elapsed
    except FileNotFoundError as exc:
        elapsed = int((time.perf_counter() - started) * 1000)
        return "", str(exc), -2, elapsed


def parse_ps(stdout: str) -> Tuple[Any, Any]:
    ands = re.findall(r"and\s*=\s*(\d+)", stdout)
    ffs = re.findall(r"(?:ff|reg)\s*=\s*(\d+)", stdout)
    return (int(ands[-1]) if ands else NA, int(ffs[-1]) if ffs else NA)


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


def short_error(stdout: str, stderr: str) -> str:
    text = (as_text(stderr) or as_text(stdout)).strip().replace("\n", " | ")
    return text[:500] if text else NA


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(block)
    except OSError:
        return NA
    return digest.hexdigest()


def git_text(repo: Path, *args: str) -> str:
    try:
        proc = subprocess.run(
            ["git", *args], cwd=repo, capture_output=True, text=True, timeout=30
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    return proc.stdout.strip() if proc.returncode == 0 else ""


def parse_b_values(text: str) -> list[int]:
    try:
        values = [int(item.strip()) for item in text.split(",") if item.strip()]
    except ValueError as exc:
        raise ValueError("--b-values must be comma-separated nonnegative integers") from exc
    if not values or any(value < 0 for value in values):
        raise ValueError("--b-values must contain nonnegative integers")
    if len(values) != len(set(values)):
        raise ValueError("--b-values must not contain duplicates")
    return values


def effective_args(base_arguments: str, b_value: int) -> str:
    """Replace -B and force exactly one -p toggle flag."""
    try:
        tokens = shlex.split(base_arguments)
    except ValueError as exc:
        raise ValueError(f"cannot parse &stran arguments: {exc}") from exc
    cleaned: list[str] = []
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token == "-B":
            if index + 1 >= len(tokens):
                raise ValueError("-B in --stran-args is missing its value")
            index += 2
            continue
        if token == "-p":
            index += 1
            continue
        cleaned.append(token)
        index += 1
    cleaned.extend(["-B", str(b_value), "-p"])
    return " ".join(cleaned)


def sum_key(lines: list[str], key: str) -> Any:
    values = [
        int(match.group(1))
        for line in lines
        if (match := re.search(rf"(?:^|[ ,]){re.escape(key)}=(\d+)", line))
    ]
    return sum(values) if values else NA


def parse_stran_metrics(stdout: str) -> Dict[str, Any]:
    result = {field: NA for field in METRIC_FIELDS}
    lines = stdout.splitlines()
    summary_lines = [
        line for line in lines
        if "Sequential direct resubstitution: rounds=" in line
    ]
    for key in (
        "rounds", "roots", "proofs", "constructed", "sig-checks",
        "sig-rejected", "sig-matched", "accepted",
    ):
        result[key.replace("-", "_")] = sum_key(summary_lines, key)

    root_lines = [
        line for line in lines if "Sequential direct root-batch profile:" in line
    ]
    scheduling = [
        match.group(1)
        for line in root_lines
        if (match := re.search(r"scheduling=([a-z0-9/-]+)", line))
    ]
    if scheduling:
        result["seq_scheduling"] = "+".join(dict.fromkeys(scheduling))
    for field, key in (
        ("root_snapshots", "snapshots"),
        ("root_closures", "batches"),
        ("root_batch_calls", "calls"),
        ("root_batch_candidates", "candidates"),
        ("root_batch_proved", "proved"),
        ("root_screened", "screened"),
    ):
        result[field] = sum_key(root_lines, key)
    maxima = [
        int(match.group(1))
        for line in root_lines
        if (match := re.search(r"(?:^|[ ,])max=(\d+)", line))
    ]
    result["root_batch_max"] = max(maxima) if maxima else NA

    yield_lines = [
        line for line in lines
        if "Sequential direct dependency-yield profile:" in line
    ]
    for count in range(65):
        result[f"dependency_yield_{count}"] = sum_key(yield_lines, f"y{count}")

    construct_lines = [
        line for line in lines if "Sequential direct construct profile:" in line
    ]
    construct_map = {
        "construct_div_pool_calls": (0, "calls"),
        "construct_div_pool_nodes": (0, "nodes"),
        "construct_dependency_calls": (1, "calls"),
        "construct_dependency_found": (1, "found"),
        "construct_dependency_attempts": (1, "attempts"),
        "construct_dependency_recipes": (1, "recipes"),
    }
    construct_totals = {field: 0 for field in construct_map}
    parsed_construct = 0
    for line in construct_lines:
        sections = line.split(";")
        if len(sections) < 2:
            continue
        for field, (section_index, key) in construct_map.items():
            match = re.search(
                rf"(?:^|[ ,]){re.escape(key)}=(\d+)", sections[section_index]
            )
            if match:
                construct_totals[field] += int(match.group(1))
        parsed_construct += 1
    if parsed_construct:
        result.update(construct_totals)

    proof_lines = [
        line for line in lines
        if "Sequential direct two-stage proof profile:" in line
    ]
    proof_totals = {
        "comb_candidates": 0,
        "comb_proved": 0,
        "scorr_candidates": 0,
        "scorr_seeded": 0,
        "scorr_proved": 0,
    }
    parsed_proof = 0
    for line in proof_lines:
        sections = line.split(";")
        if len(sections) < 3:
            continue
        comb, scorr = sections[1], sections[2]

        def integer(section: str, key: str) -> int:
            match = re.search(rf"(?:^|[ ,]){re.escape(key)}=(\d+)", section)
            return int(match.group(1)) if match else 0

        proof_totals["comb_candidates"] += integer(comb, "comb-candidates")
        proof_totals["comb_proved"] += integer(comb, "proved")
        proof_totals["scorr_candidates"] += integer(scorr, "scorr-candidates")
        proof_totals["scorr_seeded"] += integer(scorr, "seeded")
        proof_totals["scorr_proved"] += integer(scorr, "proved")
        parsed_proof += 1
    if parsed_proof:
        result.update(proof_totals)
    result.update(parse_experiment_profile(stdout))
    return result


def ratio_pct(numerator: Any, denominator: Any) -> Any:
    if not isinstance(numerator, int) or not isinstance(denominator, int) or denominator <= 0:
        return NA
    return round(100.0 * numerator / denominator, 6)


def run_dsec(abc: str, base: Path, result: Path, timeout: int) -> Tuple[str, int, str]:
    stdout, stderr, rc, elapsed = run_abc(abc, f"dsec {base} {result}", timeout)
    if rc == 0 and "Networks are equivalent" in stdout:
        status = "PASS"
    elif rc == -1:
        status = "TIMEOUT"
    elif rc == -2:
        status = "ABC_NOT_FOUND"
    else:
        status = f"FAIL({rc})"
    return status, elapsed, stdout + stderr


def write_csv_atomic(output: Path, rows: list[Dict[str, Any]]) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + ".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    os.replace(temporary, output)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Sweep &stran -B and record root coverage versus reduction."
    )
    parser.add_argument("--aig", type=Path, required=True,
                        help="one sequential AIG case")
    parser.add_argument("--abc", type=Path, default=Path("./abc"))
    parser.add_argument("--b-values", default=DEFAULT_B_VALUES)
    parser.add_argument("--stran-args", default=DEFAULT_STRAN_ARGS,
                        help="fixed args; -B is replaced and one -p is forced")
    parser.add_argument("--timeout", type=int, default=300,
                        help="seconds per &stran or dsec invocation")
    parser.add_argument("--out", type=Path,
                        default=Path("results/stran_b_scaling/b_sweep.csv"))
    parser.add_argument("--skip-dsec", action="store_true")
    parser.add_argument("--keep-artifacts", action="store_true")
    args = parser.parse_args()

    try:
        b_values = parse_b_values(args.b_values)
        effective_by_b = {
            b_value: effective_args(args.stran_args, b_value)
            for b_value in b_values
        }
    except ValueError as exc:
        sys.exit(f"[ERROR] {exc}")
    if args.timeout < 1:
        sys.exit("[ERROR] --timeout must be positive")

    aig = args.aig.expanduser().resolve()
    abc = args.abc.expanduser().resolve()
    output = args.out.expanduser().resolve()
    if not aig.is_file():
        sys.exit(f"[ERROR] AIG not found: {aig}")
    if not abc.is_file():
        sys.exit(f"[ERROR] ABC executable not found: {abc}")
    output.parent.mkdir(parents=True, exist_ok=True)

    repo = Path(__file__).resolve().parents[1]
    metadata = {
        "run_schema": RUN_SCHEMA_VERSION,
        "run_started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "git_commit": git_text(repo, "rev-parse", "HEAD") or NA,
        "git_dirty": "yes" if git_text(repo, "status", "--porcelain") else "no",
        "abc_sha256": sha256_file(abc),
        "script_sha256": sha256_file(Path(__file__).resolve()),
        "stran_args_base": args.stran_args,
        "timeout_s": args.timeout,
        "dsec_mode": "skip" if args.skip_dsec else "check",
    }

    temporary_root = Path(tempfile.mkdtemp(prefix="stran_b_scaling_"))
    artifact_root = output.parent / f"{output.stem}_artifacts"
    base = temporary_root / "base.aig"
    normalize_out, normalize_err, normalize_rc, _ = run_abc(
        str(abc), f"&read {aig}; &write {base}; &ps", args.timeout
    )
    if status_from(normalize_rc, base) != "PASS":
        shutil.rmtree(temporary_root, ignore_errors=True)
        sys.exit(f"[ERROR] normalize failed: {short_error(normalize_out, normalize_err)}")
    base_and, base_latches = parse_ps(normalize_out)

    print(f"[INFO] case={aig.name} base AND={base_and} latches={base_latches}")
    print(f"[INFO] B sweep={b_values}; all other parameters fixed")
    print("[INFO] forcing -p; each -B run uses the same paged scheduler")
    rows: list[Dict[str, Any]] = []
    try:
        for index, b_value in enumerate(b_values, start=1):
            result_aig = temporary_root / f"result_B{b_value}.aig"
            effective = effective_by_b[b_value]
            stdout, stderr, rc, elapsed = run_abc(
                str(abc),
                f"&read {base}; &stran {effective}; &write {result_aig}; &ps",
                args.timeout,
            )
            row: Dict[str, Any] = {field: NA for field in CSV_FIELDS}
            row.update(metadata)
            row.update({
                "case": aig.name,
                "b_value": b_value,
                "b_label": "all" if b_value == 0 else str(b_value),
                "stran_args_effective": effective,
                "status": status_from(rc, result_aig),
                "base_and": base_and,
                "base_latches": base_latches,
                "time_ms": elapsed,
            })
            row.update(parse_stran_metrics(stdout))
            if row["status"] == "PASS":
                final_and, final_latches = parse_ps(stdout)
                row["final_and"] = final_and
                row["final_latches"] = final_latches
                if isinstance(base_and, int) and isinstance(final_and, int):
                    row["and_reduction"] = base_and - final_and
                    row["and_reduction_pct"] = round(
                        100.0 * (base_and - final_and) / base_and, 6
                    ) if base_and else NA
                if isinstance(base_latches, int) and isinstance(final_latches, int):
                    row["latch_reduction"] = base_latches - final_latches
                if args.skip_dsec:
                    row["dsec_status"], row["dsec_time_ms"] = "SKIP", 0
                    dsec_log = ""
                else:
                    status, dsec_ms, dsec_log = run_dsec(
                        str(abc), base, result_aig, args.timeout
                    )
                    row["dsec_status"], row["dsec_time_ms"] = status, dsec_ms
                if row["dsec_status"] not in {"PASS", "SKIP"}:
                    row["error"] = f"dsec:{row['dsec_status']}"
            else:
                dsec_log = ""
                row["error"] = f"stran:{row['status']}: {short_error(stdout, stderr)}"

            row["candidate_exposure"] = row["root_batch_candidates"]
            row["sig_match_rate_pct"] = ratio_pct(row["sig_matched"], row["sig_checks"])
            row["proof_rate_pct"] = ratio_pct(
                row["root_batch_proved"], row["root_batch_candidates"]
            )
            row["accepted_rate_pct"] = ratio_pct(
                row["accepted"], row["root_batch_candidates"]
            )
            yields = [row[field] for field in DEPENDENCY_YIELD_FIELDS]
            if all(isinstance(value, int) for value in yields):
                roots_searched = sum(yields)
                roots_with_candidate = roots_searched - yields[0]
                row["roots_searched_for_candidate"] = roots_searched
                row["roots_with_candidate"] = roots_with_candidate
                row["root_coverage_pct"] = ratio_pct(
                    roots_with_candidate, roots_searched
                )
                # Build is discovered lazily after the direct lane, so this is
                # intentionally a subset of all roots rather than an error.
                row["root_build_search_pct"] = ratio_pct(
                    roots_searched, row["roots"])
            rows.append(row)

            if args.keep_artifacts:
                destination = artifact_root / f"B{b_value}"
                destination.mkdir(parents=True, exist_ok=True)
                if result_aig.is_file():
                    shutil.copy2(result_aig, destination / "result.aig")
                (destination / "stran.log").write_text(stdout + stderr, encoding="utf-8")
                (destination / "dsec.log").write_text(dsec_log, encoding="utf-8")

            valid_exposure = [
                item["candidate_exposure"] for item in rows
                if item["status"] == "PASS" and isinstance(item["candidate_exposure"], int)
            ]
            maximum = max(valid_exposure) if valid_exposure else 0
            for item in rows:
                exposure = item["candidate_exposure"]
                item["candidate_exposure_rel_pct"] = (
                    round(100.0 * exposure / maximum, 6)
                    if maximum and isinstance(exposure, int) else NA
                )
            write_csv_atomic(output, rows)
            print(
                f"[{index}/{len(b_values)}] B={row['b_label']:>3} "
                f"status={row['status']} candidates={row['candidate_exposure']} "
                f"root-coverage={row['root_coverage_pct']}% "
                f"matched={row['sig_matched']} proved={row['root_batch_proved']} "
                f"AND reduction={row['and_reduction']} time={elapsed}ms"
            )
    finally:
        shutil.rmtree(temporary_root, ignore_errors=True)

    valid_exposure = [
        row["candidate_exposure"] for row in rows
        if row["status"] == "PASS" and isinstance(row["candidate_exposure"], int)
    ]
    maximum = max(valid_exposure) if valid_exposure else 0
    for row in rows:
        exposure = row["candidate_exposure"]
        row["candidate_exposure_rel_pct"] = (
            round(100.0 * exposure / maximum, 6)
            if maximum and isinstance(exposure, int) else NA
        )
    write_csv_atomic(output, rows)
    print(f"[INFO] CSV: {output}")


if __name__ == "__main__":
    main()
