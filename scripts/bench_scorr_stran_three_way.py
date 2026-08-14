#!/usr/bin/env python3
"""Compare three independent reduction pipelines on the same AIG inputs.

For each normalized input, measure:

    1. &scorr
    2. &stran -r -p
    3. &scorr followed by &stran -r -p

The script forces exhaustive root search (``-r``) and profiling (``-p``).
Besides final sizes and wall time, the CSV captures &stran's stable experiment
profile: exact sequential Build contribution, candidate funnel, Build search
time, shared sequential-proof time, selection/commit time, and profiling
overhead.

Example:
  python3 scripts/bench_scorr_stran_three_way.py \
      --aig-dir ~/benchmark/all_test/all --abc ./abc \
      --out scorr_stran_three_way.csv --jobs 64 --timeout 12800
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, Tuple

from stran_profile import PROFILE_FIELDS, parse_experiment_profile


#DEFAULT_AIG_DIR = os.path.expanduser("~/benchmark/stran_quick_test/")
DEFAULT_AIG_DIR = os.path.expanduser("~/benchmark/all_test/all/bitlevel/")
DEFAULT_ABC = os.path.expanduser("~/abc/abc")
DEFAULT_TIMEOUT = 600
DEFAULT_JOBS = 64
DEFAULT_OUT = "scorr_stran_three_way_B64_dynamic_w1.csv"
DEFAULT_SCORR_ARGS = "-F 1 -C 100"
DEFAULT_STRAN_ARGS = (
    "-b 100 -C 100 -P root -p -V 0 -N 100 -B 64 -z -w 1 -r"
)
RUN_SCHEMA_VERSION = "all_scorr-stran-three-way-v2"
NA = "N/A"

RUN_METADATA_FIELDS = [
    "run_schema", "run_started_at", "git_commit", "git_dirty",
    "abc_sha256", "script_sha256", "scorr_args",
    "stran_args_requested", "stran_args_effective", "timeout_s", "dsec_mode",
]

STRAN_METRICS = [
    "rounds", "roots", "proofs", "sig_checks", "sig_rejected", "sig_matched",
    "accepted", "seq_scheduling", "root_snapshots", "root_closures",
    "root_batch_calls", "root_batch_candidates", "root_batch_proved",
    "root_batch_max", "comb_candidates", "comb_proved", "scorr_candidates",
    "scorr_seeded", "scorr_proved",
    *PROFILE_FIELDS,
]

PIPELINE_FIELDS = [
    "status", "dsec_status", "time_ms", "dsec_time_ms", "and", "latches",
    "and_reduction", "and_reduction_pct", "latch_reduction",
    "latch_reduction_pct",
]

CSV_FIELDS = [
    "file", *RUN_METADATA_FIELDS,
    "source_and", "source_latches", "normalize_status", "normalize_time_ms",
    "base_and", "base_latches",
    *[f"scorr_{field}" for field in PIPELINE_FIELDS],
    *[f"stran_{field}" for field in PIPELINE_FIELDS],
    *[f"stran_{field}" for field in STRAN_METRICS],
    *[f"scorr_then_stran_{field}" for field in PIPELINE_FIELDS],
    "scorr_then_stran_stran_time_ms",
    "scorr_then_stran_extra_and_reduction",
    "scorr_then_stran_extra_latch_reduction",
    *[f"scorr_then_stran_{field}" for field in STRAN_METRICS],
    "best_and", "best_pipelines", "total_time_ms", "error",
]


def as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def run_abc(abc: str, command: str, timeout: int) -> Tuple[str, str, int, int]:
    """Return stdout, stderr, return code, and wall time in milliseconds."""
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


def parse_ps(stdout: str) -> Tuple[Any, Any]:
    """Parse the final AND and FF counts from ABC's &ps output."""
    ands = re.findall(r"and\s*=\s*(\d+)", stdout)
    ffs = re.findall(r"ff\s*=\s*(\d+)", stdout)
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


def subtract(left: Any, right: Any) -> Any:
    return left - right if isinstance(left, int) and isinstance(right, int) else NA


def reduction_pct(before: Any, after: Any) -> Any:
    if not isinstance(before, int) or not isinstance(after, int) or before <= 0:
        return NA
    return round(100.0 * (before - after) / before, 6)


def short_error(stdout: str, stderr: str) -> str:
    text = (as_text(stderr) or as_text(stdout)).strip().replace("\n", " | ")
    return text[:500] if text else NA


def force_flags(arguments: str, *flags: str) -> str:
    """Return arguments with exactly one occurrence of each toggle flag."""
    try:
        tokens = shlex.split(arguments)
    except ValueError as exc:
        raise ValueError(f"cannot parse &stran arguments: {exc}") from exc
    tokens = [token for token in tokens if token not in flags]
    tokens.extend(flags)
    return " ".join(tokens)


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


def make_run_metadata(
    repo: Path,
    abc: Path,
    scorr_args: str,
    requested_stran_args: str,
    effective_stran_args: str,
    timeout: int,
    dsec: bool,
) -> Dict[str, Any]:
    return {
        "run_schema": RUN_SCHEMA_VERSION,
        "run_started_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "git_commit": git_text(repo, "rev-parse", "HEAD") or NA,
        "git_dirty": "yes" if git_text(repo, "status", "--porcelain") else "no",
        "abc_sha256": sha256_file(abc),
        "script_sha256": sha256_file(Path(__file__).resolve()),
        "scorr_args": scorr_args,
        "stran_args_requested": requested_stran_args,
        "stran_args_effective": effective_stran_args,
        "timeout_s": timeout,
        "dsec_mode": "check" if dsec else "skip",
    }


def sum_key(lines: list[str], key: str) -> Any:
    values = [
        int(match.group(1))
        for line in lines
        if (match := re.search(rf"(?:^|[ ,]){re.escape(key)}=(\d+)", line))
    ]
    return sum(values) if values else NA


def parse_stran_metrics(stdout: str) -> Dict[str, Any]:
    """Extract the scheduling and candidate counts useful to this A/B/C run."""
    result = {field: NA for field in STRAN_METRICS}
    summary_lines = [
        line for line in stdout.splitlines()
        if "Sequential direct resubstitution: rounds=" in line
    ]
    for key in ("rounds", "roots", "proofs", "sig-checks", "sig-rejected", "sig-matched", "accepted"):
        result[key.replace("-", "_")] = sum_key(summary_lines, key)

    root_lines = [
        line for line in stdout.splitlines()
        if "Sequential direct root-batch profile:" in line
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
    ):
        result[field] = sum_key(root_lines, key)
    maxima = [
        int(match.group(1))
        for line in root_lines
        if (match := re.search(r"(?:^|[ ,])max=(\d+)", line))
    ]
    result["root_batch_max"] = max(maxima) if maxima else NA

    proof_lines = [
        line for line in stdout.splitlines()
        if "Sequential direct two-stage proof profile:" in line
    ]
    totals = {
        "comb_candidates": 0,
        "comb_proved": 0,
        "scorr_candidates": 0,
        "scorr_seeded": 0,
        "scorr_proved": 0,
    }
    parsed = 0
    for line in proof_lines:
        sections = line.split(";")
        if len(sections) < 3:
            continue
        comb, scorr = sections[1], sections[2]

        def integer(section: str, key: str) -> int:
            match = re.search(rf"(?:^|[ ,]){re.escape(key)}=(\d+)", section)
            return int(match.group(1)) if match else 0

        totals["comb_candidates"] += integer(comb, "comb-candidates")
        totals["comb_proved"] += integer(comb, "proved")
        totals["scorr_candidates"] += integer(scorr, "scorr-candidates")
        totals["scorr_seeded"] += integer(scorr, "seeded")
        totals["scorr_proved"] += integer(scorr, "proved")
        parsed += 1
    if parsed:
        result.update(totals)
    result.update(parse_experiment_profile(stdout))
    return result


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


def record_size(row: Dict[str, Any], prefix: str, before_and: Any, before_latches: Any, stdout: str) -> None:
    and_count, latch_count = parse_ps(stdout)
    row[f"{prefix}_and"] = and_count
    row[f"{prefix}_latches"] = latch_count
    row[f"{prefix}_and_reduction"] = subtract(before_and, and_count)
    row[f"{prefix}_and_reduction_pct"] = reduction_pct(before_and, and_count)
    row[f"{prefix}_latch_reduction"] = subtract(before_latches, latch_count)
    row[f"{prefix}_latch_reduction_pct"] = reduction_pct(before_latches, latch_count)


def add_stran_metrics(row: Dict[str, Any], prefix: str, stdout: str) -> None:
    for field, value in parse_stran_metrics(stdout).items():
        row[f"{prefix}_{field}"] = value


def worker(task: Tuple[Any, ...]) -> Dict[str, Any]:
    (
        aig_name, relative_name, abc, scorr_args, stran_args, timeout,
        keep_artifacts, dsec, artifacts_root, run_metadata,
    ) = task
    source = Path(aig_name)
    row: Dict[str, Any] = {field: NA for field in CSV_FIELDS}
    row["file"] = relative_name
    row.update(run_metadata)
    row["source_and"], row["source_latches"] = aig_stats(source)
    errors: list[str] = []
    logs: Dict[str, str] = {}
    started = time.perf_counter()
    tag = hashlib.sha1(relative_name.encode("utf-8")).hexdigest()[:12]
    artifact_dir = Path(artifacts_root) / tag
    work_dir = artifact_dir if keep_artifacts else Path(
        tempfile.mkdtemp(prefix=f"scorr_stran_3way_{tag}_")
    )
    if keep_artifacts:
        work_dir.mkdir(parents=True, exist_ok=True)

    base = work_dir / "base.aig"
    scorr_aig = work_dir / "scorr.aig"
    stran_aig = work_dir / "stran.aig"
    combo_aig = work_dir / "scorr_then_stran.aig"

    try:
        stdout, stderr, rc, elapsed = run_abc(
            abc, f"&read {source}; &write {base}; &ps", timeout
        )
        logs["normalize.log"] = stdout + stderr
        row["normalize_time_ms"] = elapsed
        row["normalize_status"] = status_from(rc, base)
        if row["normalize_status"] != "PASS":
            errors.append(
                f"normalize:{row['normalize_status']}: {short_error(stdout, stderr)}"
            )
            return row
        row["base_and"], row["base_latches"] = parse_ps(stdout)

        # Branch A: &scorr only.
        stdout, stderr, rc, elapsed = run_abc(
            abc, f"&read {base}; &scorr {scorr_args}; &write {scorr_aig}; &ps", timeout
        )
        logs["scorr.log"] = stdout + stderr
        row["scorr_time_ms"] = elapsed
        row["scorr_status"] = status_from(rc, scorr_aig)
        if row["scorr_status"] == "PASS":
            record_size(row, "scorr", row["base_and"], row["base_latches"], stdout)
            if dsec:
                status, dsec_ms, log = run_dsec(abc, base, scorr_aig, timeout)
                row["scorr_dsec_status"], row["scorr_dsec_time_ms"] = status, dsec_ms
                logs["scorr_dsec.log"] = log
                if status != "PASS":
                    errors.append(f"scorr_dsec:{status}")
            else:
                row["scorr_dsec_status"], row["scorr_dsec_time_ms"] = "SKIP", 0
        else:
            errors.append(f"scorr:{row['scorr_status']}: {short_error(stdout, stderr)}")

        # Branch B: profiled exhaustive &stran, from the normalized input.
        stdout, stderr, rc, elapsed = run_abc(
            abc, f"&read {base}; &stran {stran_args}; &write {stran_aig}; &ps", timeout
        )
        logs["stran.log"] = stdout + stderr
        row["stran_time_ms"] = elapsed
        row["stran_status"] = status_from(rc, stran_aig)
        add_stran_metrics(row, "stran", stdout)
        if row["stran_status"] == "PASS":
            record_size(row, "stran", row["base_and"], row["base_latches"], stdout)
            if dsec:
                status, dsec_ms, log = run_dsec(abc, base, stran_aig, timeout)
                row["stran_dsec_status"], row["stran_dsec_time_ms"] = status, dsec_ms
                logs["stran_dsec.log"] = log
                if status != "PASS":
                    errors.append(f"stran_dsec:{status}")
            else:
                row["stran_dsec_status"], row["stran_dsec_time_ms"] = "SKIP", 0
        else:
            errors.append(f"stran:{row['stran_status']}: {short_error(stdout, stderr)}")

        # Branch C reuses the deterministic Branch-A result, and its reported
        # total time includes both the measured &scorr and this &stran call.
        if row["scorr_status"] == "PASS":
            stdout, stderr, rc, elapsed = run_abc(
                abc,
                f"&read {scorr_aig}; &stran {stran_args}; &write {combo_aig}; &ps",
                timeout,
            )
            logs["scorr_then_stran.log"] = stdout + stderr
            row["scorr_then_stran_stran_time_ms"] = elapsed
            row["scorr_then_stran_time_ms"] = row["scorr_time_ms"] + elapsed
            row["scorr_then_stran_status"] = status_from(rc, combo_aig)
            add_stran_metrics(row, "scorr_then_stran", stdout)
            if row["scorr_then_stran_status"] == "PASS":
                record_size(
                    row, "scorr_then_stran", row["base_and"], row["base_latches"], stdout
                )
                row["scorr_then_stran_extra_and_reduction"] = subtract(
                    row["scorr_and"], row["scorr_then_stran_and"]
                )
                row["scorr_then_stran_extra_latch_reduction"] = subtract(
                    row["scorr_latches"], row["scorr_then_stran_latches"]
                )
                if dsec:
                    status, dsec_ms, log = run_dsec(abc, base, combo_aig, timeout)
                    row["scorr_then_stran_dsec_status"] = status
                    row["scorr_then_stran_dsec_time_ms"] = dsec_ms
                    logs["scorr_then_stran_dsec.log"] = log
                    if status != "PASS":
                        errors.append(f"scorr_then_stran_dsec:{status}")
                else:
                    row["scorr_then_stran_dsec_status"] = "SKIP"
                    row["scorr_then_stran_dsec_time_ms"] = 0
            else:
                errors.append(
                    "scorr_then_stran:"
                    f"{row['scorr_then_stran_status']}: {short_error(stdout, stderr)}"
                )
        else:
            row["scorr_then_stran_status"] = "SCORR_FAILED"

        sizes = {
            name: row[f"{name}_and"]
            for name in ("scorr", "stran", "scorr_then_stran")
            if row[f"{name}_status"] == "PASS"
            and isinstance(row[f"{name}_and"], int)
        }
        if sizes:
            row["best_and"] = min(sizes.values())
            row["best_pipelines"] = "+".join(
                name for name, count in sizes.items() if count == row["best_and"]
            )
    finally:
        row["total_time_ms"] = int((time.perf_counter() - started) * 1000)
        row["error"] = " | ".join(errors) if errors else NA
        if keep_artifacts:
            for name, content in logs.items():
                (work_dir / name).write_text(content, encoding="utf-8")
        else:
            shutil.rmtree(work_dir, ignore_errors=True)

    return row


def write_csv_atomic(output: Path, rows: list[Dict[str, Any]]) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + ".tmp")
    with temporary.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    os.replace(temporary, output)


def print_summary(rows: list[Dict[str, Any]]) -> None:
    print("\n[SUMMARY] Reduction from the same normalized baseline")
    for pipeline in ("scorr", "stran", "scorr_then_stran"):
        valid = [
            row for row in rows
            if row[f"{pipeline}_status"] == "PASS"
            and row[f"{pipeline}_dsec_status"] in {"PASS", "SKIP"}
            and isinstance(row[f"{pipeline}_and_reduction"], int)
        ]
        reductions = [row[f"{pipeline}_and_reduction"] for row in valid]
        percentages = [
            row[f"{pipeline}_and_reduction_pct"] for row in valid
            if isinstance(row[f"{pipeline}_and_reduction_pct"], (int, float))
        ]
        median_pct = statistics.median(percentages) if percentages else float("nan")
        print(
            f"  {pipeline:18s} valid={len(valid):4d} "
            f"AND-reduction-sum={sum(reductions):9d} median={median_pct:8.3f}%"
        )

    winner_counts: Dict[str, int] = {}
    for row in rows:
        winner = row.get("best_pipelines")
        if winner not in (None, NA):
            winner_counts[str(winner)] = winner_counts.get(str(winner), 0) + 1
    if winner_counts:
        winners = ", ".join(
            f"{name}={count}" for name, count in sorted(winner_counts.items())
        )
        print(f"  best final AND (ties joined with +): {winners}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Compare &scorr, profiled exhaustive &stran, and their composition."
    )
    parser.add_argument("--aig-dir", default=DEFAULT_AIG_DIR)
    parser.add_argument("--abc", default=DEFAULT_ABC)
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT,
                        help="seconds per normalize/optimization/dsec ABC invocation")
    parser.add_argument("--out", default=DEFAULT_OUT)
    parser.add_argument("--jobs", type=int, default=DEFAULT_JOBS)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--scorr-args", default=DEFAULT_SCORR_ARGS)
    parser.add_argument(
        "--stran-args", default=DEFAULT_STRAN_ARGS,
        help="&stran arguments; exactly one each of -r and -p is enforced",
    )
    parser.add_argument("--keep-artifacts", action="store_true",
                        help="keep AIGs and logs next to the CSV")
    parser.add_argument("--dsec", action="store_true",
                        help="also run equivalence checks for all three results (disabled by default)")
    args = parser.parse_args()

    if args.timeout < 1 or args.jobs < 1:
        sys.exit("[ERROR] --timeout and --jobs must be positive")
    if args.limit is not None and args.limit < 0:
        sys.exit("[ERROR] --limit must be nonnegative")
    try:
        effective_stran_args = force_flags(args.stran_args, "-r", "-p")
    except ValueError as exc:
        sys.exit(f"[ERROR] {exc}")

    aig_dir = Path(args.aig_dir).expanduser().resolve()
    abc_path = Path(args.abc).expanduser().resolve()
    output = Path(args.out).expanduser().resolve()
    if not aig_dir.is_dir():
        sys.exit(f"[ERROR] AIG directory not found: {aig_dir}")
    if not abc_path.is_file():
        sys.exit(f"[ERROR] ABC executable not found: {abc_path}")
    aigs = sorted(aig_dir.rglob("*.aig"))
    if args.limit is not None:
        aigs = aigs[:args.limit]
    if not aigs:
        sys.exit(f"[ERROR] No .aig files under {aig_dir}")

    repo = Path(__file__).resolve().parents[1]
    run_metadata = make_run_metadata(
        repo, abc_path, args.scorr_args, args.stran_args, effective_stran_args,
        args.timeout, args.dsec,
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    artifacts_root = output.parent / f"{output.stem}_artifacts"
    print("[INFO] Pipelines: &scorr | &stran -r -p | &scorr -> &stran -r -p")
    print(f"[INFO] Files={len(aigs)} jobs={args.jobs} timeout={args.timeout}s")
    print(f"[INFO] &scorr args: {args.scorr_args}")
    print(f"[INFO] effective &stran args: {effective_stran_args}")
    print("[INFO] forcing exhaustive root search (-r) and experiment profiling (-p)")

    tasks = [
        (
            str(path), str(path.relative_to(aig_dir)), str(abc_path), args.scorr_args,
            effective_stran_args, args.timeout, args.keep_artifacts, args.dsec,
            str(artifacts_root), run_metadata,
        )
        for path in aigs
    ]
    rows: list[Dict[str, Any]] = []
    started = time.perf_counter()

    def collect(name: str, result: Any, done: int) -> None:
        try:
            row = result() if callable(result) else result.result()
        except Exception as exc:
            row = {field: NA for field in CSV_FIELDS}
            row["file"] = name
            row.update(run_metadata)
            row["error"] = repr(exc)
        rows.append(row)
        write_csv_atomic(output, rows)
        print(
            f"[{done:>4}/{len(tasks)}] {name:42s} "
            f"reduction AND: scorr={row['scorr_and_reduction']} "
            f"stran={row['stran_and_reduction']} "
            f"scorr+stran={row['scorr_then_stran_and_reduction']} "
            f"best={row['best_pipelines']}"
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
                for future in futures:
                    future.cancel()
                try:
                    pool.shutdown(wait=False, cancel_futures=True)
                except TypeError:
                    pool.shutdown(wait=False)
                raise
            else:
                pool.shutdown(wait=True)
    except KeyboardInterrupt:
        rows.sort(key=lambda row: row["file"])
        write_csv_atomic(output, rows)
        print(f"\n[STOP] Partial CSV with {len(rows)} completed cases: {output}")
        return

    rows.sort(key=lambda row: row["file"])
    write_csv_atomic(output, rows)
    print_summary(rows)
    print(f"[INFO] Done in {time.perf_counter() - started:.1f}s. CSV: {output}")


if __name__ == "__main__":
    main()
