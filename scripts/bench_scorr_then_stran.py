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

  # Test two-leaf transactions with an easily edited proof budget.
  python3 scripts/bench_scorr_then_stran.py \
      --aig-dir benchmark --abc ./abc --jobs 4 --timeout 1800 \
      --stran-args '-M 2 -F 1 -C 1000 -S -1 -T 1000 -N 100 -D 32 -B 64 -K 32 -Q 4 -W 8'
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, Tuple


# Edit these defaults, or override them with --scorr-args / --stran-args.
DEFAULT_AIG_DIR = os.path.expanduser("~/benchmark/all_test/all/")
DEFAULT_ABC = os.path.expanduser("~/abc/abc")
DEFAULT_TIMEOUT = 12800
DEFAULT_JOBS = 64
DEFAULT_OUT = "scorr_then_stran.csv"
# Keep the baseline at the user's normal &scorr defaults.  Do not add -r:
# it toggles implication rings *off* because they are enabled by default.
DEFAULT_SCORR_ARGS = "-F 1 -C 200"
DEFAULT_STRAN_ARGS = "-M 1 -F 1 -C 1000 -S -1 -T 1000 -N 100 -D 32 -B 64 -K 32 -Q 4 -W 8"
NA = "N/A"


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
        return exc.stdout or "", "TIMEOUT", -1, elapsed
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
    return result


def short_error(stdout: str, stderr: str) -> str:
    text = (stderr or stdout).strip().replace("\n", " | ")
    return text[:500] if text else NA


def worker(task: Tuple[str, str, str, str, int, str, bool, str]) -> Dict[str, Any]:
    aig_name, relative_name, abc, scorr_args, timeout, stran_args, keep_artifacts, artifacts_root = task
    source = Path(aig_name)
    source_and, source_latches = aig_stats(source)
    row: Dict[str, Any] = {
        "file": relative_name,
        "source_and": source_and,
        "source_latches": source_latches,
        "scorr_status": NA,
        "stran_status": NA,
        "dsec_status": NA,
        "normalize_time_ms": NA,
        "scorr_time_ms": NA,
        "stran_time_ms": NA,
        "dsec_time_ms": NA,
        "total_time_ms": NA,
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
    started = time.perf_counter()
    tag = hashlib.sha1(relative_name.encode("utf-8")).hexdigest()[:12]
    artifact_dir = Path(artifacts_root) / tag
    work_dir = artifact_dir if keep_artifacts else Path(tempfile.mkdtemp(prefix=f"scorr_stran_{tag}_"))
    if keep_artifacts:
        work_dir.mkdir(parents=True, exist_ok=True)
    norm_out = norm_err = scorr_out = scorr_err = stran_out = stran_err = dsec_out = dsec_err = ""

    try:
        # Rewriting the source once makes all AIGER names consistent.  dsec
        # then compares this normalized baseline with the final result.
        base = work_dir / "base.aig"
        scorr = work_dir / "scorr.aig"
        final = work_dir / "final.aig"
        norm_out, norm_err, norm_rc, norm_ms = run_abc(
            abc, f"&read {source}; &write {base}", timeout
        )
        row["normalize_time_ms"] = norm_ms
        norm_status = status_from(norm_rc, base)
        if norm_status != "PASS":
            row["error"] = f"normalize:{norm_status}: {short_error(norm_out, norm_err)}"
            return row

        scorr_out, scorr_err, scorr_rc, scorr_ms = run_abc(
            abc, f"&read {base}; &scorr {scorr_args}; &write {scorr}", timeout
        )
        row["scorr_time_ms"] = scorr_ms
        row["scorr_status"] = status_from(scorr_rc, scorr)
        if row["scorr_status"] != "PASS":
            row["error"] = f"scorr:{row['scorr_status']}: {short_error(scorr_out, scorr_err)}"
            return row
        row["scorr_and"], row["scorr_latches"] = aig_stats(scorr)
        row["scorr_and_reduction"] = subtract(source_and, row["scorr_and"])
        row["scorr_latch_reduction"] = subtract(source_latches, row["scorr_latches"])

        # This starts strictly from the completed &scorr output.  &stran's
        # own time includes its per-candidate sequential proof calls.
        stran_out, stran_err, stran_rc, stran_ms = run_abc(
            abc, f"&read {scorr}; &stran {stran_args}; &write {final}", timeout
        )
        row["stran_time_ms"] = stran_ms
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

        dsec_out, dsec_err, dsec_rc, dsec_ms = run_abc(
            abc, f"dsec {base} {final}", timeout
        )
        row["dsec_time_ms"] = dsec_ms
        row["dsec_status"] = (
            "PASS" if dsec_rc == 0 and "Networks are equivalent" in dsec_out
            else "TIMEOUT" if dsec_rc == -1
            else f"FAIL({dsec_rc})"
        )
        if row["dsec_status"] != "PASS":
            row["error"] = f"dsec:{row['dsec_status']}: {short_error(dsec_out, dsec_err)}"

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
    "file", "source_and", "source_latches", "scorr_status", "stran_status", "dsec_status",
    "normalize_time_ms", "scorr_time_ms", "stran_time_ms", "dsec_time_ms", "total_time_ms",
    "scorr_and", "scorr_latches", "stran_and", "stran_latches",
    "scorr_and_reduction", "scorr_latch_reduction",
    "stran_extra_and_reduction", "stran_extra_latch_reduction",
    "total_and_reduction", "total_latch_reduction",
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
    args = parser.parse_args()

    aig_dir = Path(args.aig_dir).expanduser().resolve()
    abc = str(Path(args.abc).expanduser().resolve())
    output = Path(args.out).expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    if not aig_dir.is_dir():
        sys.exit(f"[ERROR] AIG directory not found: {aig_dir}")
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
    print(f"[INFO] &stran args: {args.stran_args}")

    tasks = [
        (str(path), str(path.relative_to(aig_dir)), abc, args.scorr_args, args.timeout,
         args.stran_args, args.keep_artifacts, str(output.parent / f"{output.stem}_artifacts"))
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
