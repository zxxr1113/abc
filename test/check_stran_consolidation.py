#!/usr/bin/env python3
"""Paired integration validation; retain loaded inputs, products and independent DSEC."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def aig_structure_sha(path):
    # Parse the actual binary AIG boundary, not a search for the byte 'c'
    # (which may occur inside an AND delta). Exclude ABC's timestamp comment.
    data = Path(path).read_bytes()
    pos = data.index(b"\n") + 1
    fields = data[:pos].split()
    assert len(fields) == 6 and fields[0] == b"aig", fields
    _, _, latches, outputs, ands = map(int, fields[1:])
    for _ in range(latches + outputs):
        pos = data.index(b"\n", pos) + 1
    for _ in range(2 * ands):
        while data[pos] & 128:
            pos += 1
        pos += 1
    return hashlib.sha256(data[:pos]).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--control", required=True)
    p.add_argument("--candidate", required=True)
    p.add_argument("--inputs", required=True, help="JSON mapping name to path")
    p.add_argument("--out", required=True)
    p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--timeout", type=int, default=1800)
    args = p.parse_args()
    assert 1 <= args.jobs <= 16 and args.timeout > 0
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=False)
    inputs = json.loads(Path(args.inputs).read_text())
    env = {k: v for k, v in os.environ.items() if not k.startswith("ABC_")}
    env.update(ABC_CEX_MODE="2", ABC_CEX_COMPRESS="4", ABC_CEX_PACK_FAST="2",
               ABC_CEX_PROJECT_ALL="0")
    base = ("-F 1 -C 1000 -b 100 -S -1 -N 20 -B 16 -T 8 -D 1 -K 8 "
            "-Q 4 -W 8 -q 20 -j 5 -w 8 -V 0 -E 742531093 -d -k -J -O 0 -L 4 -H 2 -p")
    arms = {
        "control": (args.control, ""),
        "exact": (args.candidate, ""),
        "cache": (args.candidate, "-A window-cache=1"),
        "factor": (args.candidate, "-A window-cache=1 -A window-factor=1"),
        "speed": (args.candidate, "-A profile=strict-speed -A window-cache=1 -A window-factor=1"),
    }
    manifest = dict(host=socket.gethostname(), started=time.time(), inputs=inputs,
                    input_sha={k: sha(v) for k, v in inputs.items()},
                    arms=arms, base=base, jobs=args.jobs, timeout=args.timeout,
                    env={k: v for k, v in env.items() if k.startswith("ABC_")})
    for binary in (args.control, args.candidate):
        record = json.loads(Path(binary + ".build.json").read_text())
        assert record["host"] == socket.gethostname()
        assert record["binary_sha256"] == sha(binary)
        subprocess.run(["ldd", binary], check=True, stdout=subprocess.DEVNULL)
        manifest[binary] = record
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2))

    def execute(binary, command, log):
        started = time.monotonic()
        with log.open("w") as f:
            try:
                r = subprocess.run([binary, "-q", command], env=env,
                                   stdout=f, stderr=subprocess.STDOUT, timeout=args.timeout)
                status = "OK" if r.returncode == 0 else "ERROR"
            except subprocess.TimeoutExpired:
                status = "TIMEOUT"
        return status, time.monotonic() - started

    def case(item):
        name, source = item
        directory = out / name
        directory.mkdir()
        results = {}
        for arm, (binary, extra) in arms.items():
            before, after = directory / (arm+"-loaded.aig"), directory / (arm+"-after.aig")
            command = f"&read {source}; &write {before}; &stran2 {base} {extra}; &write {after}; &ps"
            status, seconds = execute(binary, command, directory/(arm+".log"))
            result = dict(status=status, wall_seconds=seconds, command=command)
            if status == "OK" and after.exists():
                result.update(loaded_sha=sha(before), after_sha=sha(after),
                              loaded_structure_sha=aig_structure_sha(before),
                              after_structure_sha=aig_structure_sha(after))
                dsec_cmd = f"dsec {before} {after}"
                ds, dt = execute(args.control, dsec_cmd, directory/(arm+"-dsec.log"))
                text = (directory/(arm+"-dsec.log")).read_text()
                result.update(dsec="PASS" if ds == "OK" and "Networks are equivalent" in text
                              else ds if ds != "OK" else "UNDECIDED",
                              dsec_seconds=dt, dsec_command=dsec_cmd)
            else:
                result["dsec"] = "NOT_RUN"
                if status == "OK":
                    result["status"] = "NO_PRODUCT"
            results[arm] = result
            (directory/"results.json").write_text(json.dumps(results, indent=2))
            print(name, arm, result["status"], result["dsec"], round(seconds, 3), flush=True)
        results["exact_identity"] = all(
            results[a].get("after_structure_sha") == results["control"].get("after_structure_sha")
            and results[a]["dsec"] == "PASS" for a in ("exact", "cache"))
        results["loaded_identity"] = len({results[a].get("loaded_structure_sha") for a in arms}) == 1
        (directory/"results.json").write_text(json.dumps(results, indent=2))
        return name, results

    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        results = dict(pool.map(case, inputs.items()))
    (out/"results.json").write_text(json.dumps(results, indent=2))
    passed = all(r["exact_identity"] and r["loaded_identity"] and
                 all(r[a]["dsec"] == "PASS" for a in arms) for r in results.values())
    print("PASS" if passed else "INCOMPLETE_OR_FAILED", flush=True)
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
