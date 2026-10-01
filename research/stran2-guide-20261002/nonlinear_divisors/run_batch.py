#!/usr/bin/env python3
"""Run frozen packaged cases in child processes; retain every timeout/failure."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import time

from prototype import Config, PACKAGE, HERE, asdict, sha, write_json

PILOT = ["005_b03.aig", "044_i2c.aig", "041_des_area.aig", "034_b20_opt.aig",
         "045_mem_ctrl.aig", "060_wb_dma.aig"]


def aggregate(rows):
    completed = [r for r in rows if r.get("status") == "COMPLETE"]
    validated = [r for r in completed if r.get("product", {}).get("validated_standalone_noncomb_build_gain") is not None]
    beneficiaries = [r for r in validated if r["product"]["validated_standalone_noncomb_build_gain"] > 0]

    def stats(cases):
        gain = sum(c["product"]["validated_standalone_noncomb_build_gain"] for c in cases)
        return dict(cases=len(cases), and_gain=gain,
                    equal_case_percent=(100 * sum(c["product"]["validated_standalone_noncomb_build_gain"] / c["loaded_and"] for c in cases) / len(cases)) if cases else None,
                    weighted_percent=(100 * gain / sum(c["loaded_and"] for c in cases)) if cases else None)

    largest = max(validated, key=lambda c: c["product"]["validated_standalone_noncomb_build_gain"], default=None)
    size_ranges = [("lt1k", 0, 1000), ("1k_to_10k", 1000, 10000), ("10k_to_100k", 10000, 100000), ("ge100k", 100000, float("inf"))]
    return dict(attempted=len(rows), completed=len(completed), validated=len(validated),
                benefited_cases=[r["file"] for r in beneficiaries],
                statuses={status: sum(r.get("status") == status for r in rows) for status in sorted({r.get("status", "MISSING") for r in rows})},
                standalone_product=stats(validated),
                largest_contributor=largest["file"] if largest else None,
                excluding_largest_contributor=stats([r for r in validated if r is not largest]),
                by_loaded_size={label: stats([r for r in validated if lo <= r["loaded_and"] < hi]) for label, lo, hi in size_ranges},
                scope="standalone reset-image proof products; production/native comparison NOT_RUN",
                missing_data_are_zero=False)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    cohort = p.add_mutually_exclusive_group(required=True)
    cohort.add_argument("--pilot", action="store_true")
    cohort.add_argument("--all", action="store_true")
    cohort.add_argument("--cases", nargs="+")
    p.add_argument("--solver", type=Path, required=True)
    p.add_argument("--abc", type=Path)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--workers", type=int, default=1)
    p.add_argument("--dsec-seconds", type=float, default=120.0)
    for key, value in asdict(Config()).items():
        p.add_argument("--" + key.replace("_", "-"), type=type(value), default=value)
    a = p.parse_args()
    if a.workers < 1:
        p.error("workers must be positive")
    config = Config(**{key: getattr(a, key) for key in asdict(Config())})
    config.validate()
    manifest = json.loads((PACKAGE / "cases.json").read_text())
    names = PILOT if a.pilot else [r["file"] for r in manifest["cases"]] if a.all else a.cases
    if len(set(names)) != len(names) or not set(names) <= {r["file"] for r in manifest["cases"]}:
        p.error("duplicate or unknown packaged cases")
    a.out.mkdir(parents=True, exist_ok=False)
    plan = dict(schema=1, cases=names, config=asdict(config), workers=a.workers,
                solver=str(a.solver.resolve()), solver_sha256=sha(a.solver),
                abc=str(a.abc.resolve()) if a.abc else None,
                dsec_seconds=a.dsec_seconds,
                source_hashes={f.name: sha(f) for f in HERE.glob("*.py")},
                manifest_sha256=sha(PACKAGE / "cases.json"))
    runtime_files = [HERE / "prototype.py", HERE / "product.py", HERE / "run_batch.py",
                     PACKAGE / "seq_cut_image/diagnose.py",
                     PACKAGE / "seq_care_synthesis/scan_exact_care.py",
                     PACKAGE / "seq_care_synthesis/guide.py",
                     PACKAGE / "teacher_adaptive_tools/teacher_bmc.py"]
    plan["runtime_source_hashes"] = {str(f.relative_to(PACKAGE)): sha(f) for f in runtime_files}
    for source in runtime_files:
        dest = a.out / "source" / source.relative_to(PACKAGE)
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
    plan["abc_sha256"] = sha(a.abc) if a.abc else None
    write_json(a.out / "plan.json", plan)

    def work(name):
        target = a.out / Path(name).stem
        command = [sys.executable, str(HERE / "prototype.py"), "--case", name,
                   "--solver", str(a.solver.resolve()), "--out", str(target.resolve())]
        if a.abc:
            command.extend(["--abc", str(a.abc.resolve()), "--dsec-seconds", str(a.dsec_seconds)])
        for key, value in asdict(config).items():
            command.extend(["--" + key.replace("_", "-"), str(value)])
        start = time.monotonic()
        with (a.out / (Path(name).stem + ".driver.log")).open("w") as log:
            process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
            # Dedicated case transform budget plus two independent DSEC limits.
            limit = config.wall_seconds + (2 * a.dsec_seconds if a.abc else 0) + 15
            try:
                rc = process.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                rc = 124
        result_path = target / "result.json"
        if result_path.exists():
            row = json.loads(result_path.read_text())
        else:
            row = dict(schema=1, file=name, status="TIMEOUT" if rc == 124 else "ERROR",
                       error="driver deadline or child without result", measured_seq_build_gain=None)
        row["driver"] = dict(exit_code=rc, wall_s=time.monotonic() - start, command=command)
        if rc != 0 and row.get("status") == "COMPLETE":
            row["status"] = "ERROR"
            row["error"] = "complete result with nonzero child exit"
        write_json(a.out / (Path(name).stem + ".attempt.json"), row)
        return row

    rows = []
    with ThreadPoolExecutor(max_workers=a.workers) as executor:
        futures = {executor.submit(work, name): name for name in names}
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            rows.sort(key=lambda r: names.index(r["file"]))
            write_json(a.out / "results.json", rows)
            write_json(a.out / "summary.json", aggregate(rows))
            print(json.dumps(dict(file=row["file"], status=row["status"], product=row.get("product", {})), sort_keys=True), flush=True)
    source_drift = [str(f.relative_to(PACKAGE)) for f in runtime_files
                    if sha(f) != plan["runtime_source_hashes"][str(f.relative_to(PACKAGE))]]
    write_json(a.out / "source_integrity.json", dict(status="PASS" if not source_drift else "FAIL", changed=source_drift))
    if source_drift:
        raise RuntimeError("runtime sources changed during frozen batch")
    print(json.dumps(aggregate(rows), sort_keys=True))
    return 0 if all(r["status"] == "COMPLETE" for r in rows) else 1


if __name__ == "__main__":
    raise SystemExit(main())
