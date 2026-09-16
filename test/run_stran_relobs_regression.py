#!/usr/bin/env python3
"""Independent tiny-product reachability and integrated output-tail regression.

Usage: python3 test/run_stran_relobs_regression.py ABC OUTPUT_DIRECTORY
All latch initial values in these BLIF witnesses are explicitly zero.
"""
import collections
import itertools
import json
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from stran_profile import parse_experiment_profile, validate_profile_accounting


def read_aig(path):
    data = path.read_bytes()
    end = data.index(b"\n")
    magic, m, ni, nl, no, na = data[:end].split()
    assert magic == b"aig"
    m, ni, nl, no, na = map(int, (m, ni, nl, no, na))
    pos = end + 1
    latches, outputs, gates = [], [], []
    for i in range(nl + no):
        end = data.index(b"\n", pos)
        line = list(map(int, data[pos:end].split()))
        assert len(line) == 1 or (i < nl and line[1] == 0)
        (latches if i < nl else outputs).append(line[0])
        pos = end + 1
    def uint():
        nonlocal pos
        value = shift = 0
        while True:
            b = data[pos]; pos += 1
            value |= (b & 127) << shift
            if b < 128:
                return value
            shift += 7
    for i in range(na):
        lhs = 2 * (ni + nl + i + 1)
        a = lhs - uint(); b = a - uint()
        gates.append((lhs // 2, a, b))
    return m, ni, nl, outputs, latches, gates


def step(g, state, inputs):
    m, ni, nl, outputs, latches, gates = g
    v = [0] * (m + 1)
    v[1:ni+1] = inputs
    v[ni+1:ni+nl+1] = state
    def lit(x): return v[x // 2] ^ (x & 1)
    for i, a, b in gates:
        v[i] = lit(a) & lit(b)
    return tuple(map(lit, outputs)), tuple(map(lit, latches))


def product_bfs(a, b):
    assert a[1] == b[1] and len(a[3]) == len(b[3])
    initial = ((0,) * a[2], (0,) * b[2])
    queue = collections.deque([(initial, 0)])
    seen = {initial}
    divergent = False
    while queue:
        (sa, sb), depth = queue.popleft()
        divergent |= sa != sb
        for inputs in itertools.product((0, 1), repeat=a[1]):
            oa, na = step(a, sa, inputs); ob, nb = step(b, sb, inputs)
            if oa != ob:
                return dict(equivalent=False, first_bad_frame=depth, states=len(seen), divergent=divergent)
            pair = na, nb
            if pair not in seen:
                seen.add(pair); queue.append((pair, depth + 1))
    return dict(equivalent=True, states=len(seen), divergent=divergent)


def run(abc, command, logfile, env):
    p = subprocess.run([str(abc), "-q", command], text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=1800, env=env, cwd=logfile.parent)
    logfile.write_text(command + "\n" + p.stdout)
    assert p.returncode == 0, p.stdout[-2000:]
    return p.stdout


def main():
    abc, out = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy(); env["ABC_RELOBS_DUMP"] = str(out)
    results = {}
    for build in (0, 1):
        blif = out / f"valid_data_{build}.blif"
        blif.write_text(".model valid_data\n.inputs en d" + (" e" if build else "") +
                        "\n.outputs y\n.latch en valid 0\n.latch root data 0\n.names valid data y\n11 1\n" +
                        (".names en d e root\n111 1\n" if build else ".names en d root\n11 1\n") + ".end\n")
        for mode in (0, 6, 27):
            base, final = out / f"base{build}-{mode}.aig", out / f"final{build}-{mode}.aig"
            text = run(abc, f"read_blif {blif}; strash; &get; &write -s {base}; &stran2 -F 2 -C 1000 -Y 1 -R {mode} -p; &write -s {final}",
                       out / f"online-{build}-{mode}.log", env)
            ga, gb = read_aig(base), read_aig(final)
            proof = product_bfs(ga, gb)
            assert proof["equivalent"]
            if mode == 6:
                # Initial scorr can already prove valid&data=data in this
                # particular source, deleting valid and the opportunity.  The
                # explicit local semantic/Build test is separate below.
                if "relobs-commit " in text:
                    assert "state-status=0" in text and "window-status=0" in text
            if mode == 27:
                assert "tracebuild-summary mode=27 boundary=output" in text
            profile = parse_experiment_profile(text)
            validate_profile_accounting(profile, len(gb[-1]))
            results[f"online-{build}-{mode}"] = dict(proof, before=len(ga[-1]), after=len(gb[-1]))
            sec = run(abc, f"dsec {base} {final}", out / f"dsec-{build}-{mode}.log", env)
            assert "Networks are equivalent" in sec
    # Independent exhaustive proof of the explicit positive and late-negative
    # products emitted by the C self-test, including all possible input traces.
    for before in (sorted(out.glob("*-witness-before.aig")) + sorted(out.glob("*-negative-before.aig"))
                   + sorted(out.glob("*-tail-before.aig"))):
        after = before.with_name(before.name.replace("before", "after"))
        proof = product_bfs(read_aig(before), read_aig(after))
        if "negative" in before.name:
            assert not proof["equivalent"] and proof["first_bad_frame"] == 10
        else:
            assert proof["equivalent"] and proof["divergent"]
        results[before.name] = proof
    (out / "results.json").write_text(json.dumps(results, indent=2))
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
