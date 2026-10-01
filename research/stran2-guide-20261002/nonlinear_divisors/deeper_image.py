#!/usr/bin/env python3
"""Recheck immutable recipes with a complete finite-image sufficient proof.

For depth k: root XOR recipe is UNSAT in each reset frame 0..k-1 and
in frame k after k original transitions from unrestricted predecessor state.
Every frame gets fresh independent PI. This covers all reset-reachable times;
it is neither bounded-only BMC nor induction using the candidate as a premise.
SAT at the unrestricted image is NOT a reachable counterexample or teacher.
No search, candidate mutation, graph replacement, or product selection occurs.
"""
from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
STATUS = {-1: "UNSAT", 0: "UNKNOWN", 1: "SAT"}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def json_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def write_json(path, value):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def load_runtime(package):
    """Import the explicitly named frozen source snapshot, never cwd defaults."""
    path = Path(package).resolve() / "nonlinear_divisors/prototype.py"
    require(path.is_file(), "missing explicitly selected prototype snapshot")
    name = "_stran2_frozen_prototype_" + sha(path)[:16]
    if name not in sys.modules:
        spec = importlib.util.spec_from_file_location(name, path)
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
    module = sys.modules[name]
    require(Path(module.__file__).resolve() == path, "runtime path collision; use a fresh process")
    # prototype.py imports three named dependencies. Refuse stale cached modules
    # from some other run, even when their bytes happen to be equal.
    for key in ("diagnose", "scan_exact_care", "guide", "teacher_bmc"):
        dep = sys.modules[key]
        require(Path(dep.__file__).resolve().is_relative_to(Path(package).resolve()),
                "dependency loaded outside explicit frozen snapshot: " + key)
    return module


def validate_aiger(a):
    require(all(type(v) is int and v >= 0 for v in (a.ni, a.nl, a.m, a.na)), "invalid graph sizes")
    require(a.m == a.ni + a.nl + a.na and a.na == len(a.gates), "non-dense graph")
    require(len(a.latches) == len(a.initial) == a.nl, "latch/reset interface mismatch")
    require(all(v == 0 for v in a.initial), "only ordinary zero-reset circuits supported")
    for node, gate in enumerate(a.gates, a.ni + a.nl + 1):
        require(len(gate) == 2 and all(type(x) is int and 0 <= x < 2 * node for x in gate),
                "non-topological gate")
    require(all(type(x) is int and 0 <= x < 2 * (a.m + 1) for x in a.latches + a.outputs),
            "latch/output literal out of range")


def compile_frames(a, depth, graph_factory, deadline=None):
    """Return independently quantified reset prefix and unrestricted image frames.

    Frame maps retain original AIG node IDs. Latch *input* literals are always
    evaluated in the immediately previous frame, including constants/phase.
    The image chain has no reset restrictions or candidate assumptions.
    """
    require(type(depth) is int and depth >= 1, "positive integer image depth required")
    validate_aiger(a)
    g = graph_factory()

    def chain(reset, count):
        state = [0] * a.nl if reset else [g.pi() for _ in range(a.nl)]
        frames = []
        for frame in range(count):
            if deadline is not None:
                deadline.remaining()
            pi = [g.pi() for _ in range(a.ni)]
            mapped = [0] + pi + state
            for node, (x, y) in enumerate(a.gates, a.ni + a.nl + 1):
                if deadline is not None and node % 256 == 0:
                    deadline.remaining()
                mapped.append(g.land(mapped[x // 2] ^ (x & 1), mapped[y // 2] ^ (y & 1)))
            frames.append(dict(frame=frame, pi=pi, state=state, mapping=mapped))
            state = [mapped[x // 2] ^ (x & 1) for x in a.latches]
        return frames

    reset = chain(True, depth)
    image = chain(False, depth + 1)
    all_pi = [lit for frame in reset + image for lit in frame["pi"]]
    require(len(all_pi) == len(set(all_pi)), "PI variables reused across frames")
    require(not (set(all_pi) & set(image[0]["state"])), "PI and predecessor state aliased")
    return g, reset, image


def validate_candidate(a, c):
    root, recipe, out = c["root"], c["recipe"], c["out"]
    require(type(root) is int and 0 < root <= a.m, "candidate root out of range")
    require(isinstance(recipe, list) and len(recipe) % 2 == 0, "invalid recipe shape")

    def literal(code, built):
        require(type(code) is int, "noninteger recipe literal")
        if code >= 0:
            require(code // 2 < root, "cyclic or out-of-range recipe divisor")
        else:
            require(code <= -2 and (-code - 2) // 2 < built, "forward/cyclic recipe reference")

    for i, code in enumerate(recipe):
        literal(code, i // 2)
    literal(out, len(recipe) // 2)


def make_queries(a, candidates, depth, runtime, deadline=None):
    g, reset, image = compile_frames(a, depth, runtime.Graph, deadline)
    order, queries = [], []
    phases = [("reset", f["frame"], f["mapping"]) for f in reset]
    phases.append(("unrestricted_image", depth, image[-1]["mapping"]))
    for index, c in candidates:
        if deadline is not None:
            deadline.remaining()
        validate_candidate(a, c)
        for phase, frame, mapping in phases:
            new = runtime.graph_recipe(g, mapping, c["recipe"], c["out"])
            diff = g.xor(mapping[c["root"]], new)
            order.append(dict(query=len(queries), source_candidate_index=index, root=c["root"],
                              phase=phase, frame=frame, miter_literal=diff))
            queries.append([diff])
    return g, queries, order, dict(reset=reset, unrestricted_image=image)


def verify_frozen(run, case_dir, solver):
    """Bind source, raw proof rows, candidate recipes, and immutable input bytes."""
    run, case_dir, solver = map(lambda p: Path(p).resolve(), (run, case_dir, solver))
    require(case_dir.parent == run, "case directory is not an immediate child of frozen run")
    plan = json.loads((run / "plan.json").read_text())
    integrity = json.loads((run / "source_integrity.json").read_text())
    require(integrity["status"] == "PASS" and not integrity["changed"], "source cohort not frozen cleanly")
    provenance = json.loads((case_dir / "provenance.json").read_text())
    result = json.loads((case_dir / "result.json").read_text())
    require(result["status"] == "COMPLETE", "only completed frozen cases are eligible")
    require(result["file"] in plan["cases"] and Path(result["file"]).stem == case_dir.name,
            "case identity mismatch")
    package = run / "source"
    bound = {}

    def bind(path, expected=None):
        path = Path(path).resolve()
        actual = sha(path)
        require(expected is None or actual == expected, "frozen hash mismatch: " + str(path))
        bound[str(path)] = actual
        return actual

    for relative, expected in plan["runtime_source_hashes"].items():
        bind(package / relative, expected)
    require(provenance["prototype_sha256"] == plan["runtime_source_hashes"]["nonlinear_divisors/prototype.py"],
            "candidate/source prototype mismatch")
    for relative, expected in provenance["dependencies"].items():
        require(plan["runtime_source_hashes"][relative] == expected, "candidate/source dependency mismatch")
    require(provenance["config"] == plan["config"], "candidate search configuration mismatch")
    source = Path(provenance["input"]).resolve()
    bind(source, provenance["input_sha256"])
    require(result["input_sha256"] == provenance["input_sha256"], "result/input identity mismatch")
    require(sha(solver) == provenance["solver_sha256"] == plan["solver_sha256"], "solver changed")
    bind(solver, plan["solver_sha256"])
    for file in ("plan.json", "source_integrity.json"):
        bind(run / file)
    for file in ("provenance.json", "result.json", "candidates.json", "candidates.unproved.json", "query_order.json"):
        bind(case_dir / file)
    qstats = result["proof_queries"]
    require(qstats["conflicts_per_query"] == 1000, "source conflict limit changed")
    for file, key in (("obligations.cnf", "cnf_sha256"), ("obligations.queries", "queries_sha256"),
                      ("obligations.results.csv", "results_sha256")):
        bind(case_dir / file, qstats[key])
    candidates = json.loads((case_dir / "candidates.json").read_text())
    unproved = json.loads((case_dir / "candidates.unproved.json").read_text())
    order = json.loads((case_dir / "query_order.json").read_text())
    with (case_dir / "obligations.results.csv").open() as stream:
        rows = list(csv.DictReader(stream))
    require(len(candidates) == len(unproved) == result["candidate_count"], "candidate count mismatch")
    require(len(rows) == len(order) == 3 * len(candidates), "source query count mismatch")
    for i, (c, old) in enumerate(zip(candidates, unproved)):
        require(all(c[k] == v for k, v in old.items()), "frozen recipe changed after search")
        for j, phase in enumerate(("free", "reset", "step")):
            q = 3 * i + j
            require(order[q]["query"] == int(rows[q]["query"]) == q and order[q]["candidate"] == i and
                    order[q]["root"] == c["root"] and order[q]["phase"] == phase, "source query identity mismatch")
            require(c["proof"][phase] == STATUS[int(rows[q]["result"])], "source proof/result mismatch")
    return package, source, candidates, result, bound


def assert_unchanged(bound):
    for path, expected in bound.items():
        require(sha(path) == expected, "frozen evidence changed during recheck: " + path)


def recheck(run, case_dir, solver, out, depth=2, seconds=120.0):
    require(depth == 2, "this frozen recheck protocol uses depth 2 only")
    require(seconds == 120.0, "this frozen recheck protocol uses 120 seconds per case")
    started = time.monotonic()
    package, source, candidates, old_result, bound = verify_frozen(run, case_dir, solver)
    runtime = load_runtime(package)
    deadline = runtime.Deadline(seconds)
    deadline.start, deadline.end = started, started + seconds
    deadline.remaining()
    a = runtime.Aiger(source)
    validate_aiger(a)
    selected = [(i, c) for i, c in enumerate(candidates) if c["proof"]["step"] == "SAT"]
    provenance = dict(schema=1, source_run=str(Path(run).resolve()), source_case=str(Path(case_dir).resolve()),
                      source_identity=bound, input_sha256=sha(source),
                      rechecker_sha256=sha(__file__), depth=depth, wall_seconds=seconds,
                      conflicts_per_query=1000, candidate_count=len(candidates),
                      selected_indices=[i for i, c in selected], selection_rule="source proof.step == SAT",
                      candidate_search="NOT_RERUN", source_candidates_mutated=False,
                      proof_boundary="reset frames 0,1 AND unrestricted two-transition image at frame 2",
                      unrestricted_image_SAT_is_reachable_witness=False)
    write_json(out / "provenance.json", provenance)
    shutil.copyfile(__file__, out / "rechecker.source.py")
    for index, c in selected:
        deadline.remaining()
        validate_candidate(a, c)
        w = c["free_witness"]
        require(c["proof"]["free"] == "SAT" and c["proof"]["free_witness_replayed"], "missing free SAT evidence")
        require(w["kind"] == "free_PI_RO" and w["replay"] == "PASS", "unsupported source witness")
        require(all(type(v) is int and v in (0, 1) for v in w["inputs"] + w["state"]), "nonboolean witness")
        values = a.step(w["inputs"], w["state"])[2]
        replacement = runtime.recipe_eval(c["recipe"], c["out"], values)
        require(values[c["root"]] != replacement and values[c["root"]] == w["root"] and
                replacement == w["replacement"], "free witness replay mismatch")
        require(c["conservative_gain"] > 0 and c["fresh_gates"] > 0, "not a positive-costed Build recipe")
    g, queries, order, frames = make_queries(a, selected, depth, runtime, deadline)
    write_json(out / "query_order.json", order)
    write_json(out / "frames.json", frames)
    write_json(out / "progress.json", dict(stage="queries", selected=len(selected), queries=len(queries),
                                           wall_s=time.monotonic() - started))
    answers, qstats = runtime.run_queries(g, queries, out, solver, deadline)
    records, qualified, groups = [], [], Counter()
    for position, (index, c) in enumerate(selected):
        rs = answers[position * (depth + 1):(position + 1) * (depth + 1)]
        good = all(x == -1 for x in rs)
        groups[tuple(STATUS[x] for x in rs)] += 1
        record = dict(source_candidate_index=index, source_candidate_sha256=json_sha(c), candidate=c,
                      free_witness_replayed=True,
                      recheck=dict(reset_prefix=[STATUS[x] for x in rs[:-1]], unrestricted_image=STATUS[rs[-1]],
                                   depth=depth, complete_sufficient_proof=good,
                                   sequential_relation="PROVED_RESET_PREFIX_IMAGE" if good else "NOT_PROVED",
                                   unrestricted_image_SAT_is_reachable_witness=False),
                      qualified_two_step_opportunity=good, production_seq_proof="NOT_RUN",
                      product_selection="NOT_RUN", exact_selected_set_gain=None, main_metric_eligible=False)
        records.append(record)
        if good:
            qualified.append(record)
    assert_unchanged(bound)
    deadline.remaining()
    write_json(out / "candidates.rechecked.json", records)
    write_json(out / "qualified.json", qualified)
    best = {}
    for row in qualified:
        c = row["candidate"]
        if c["root"] not in best or runtime.candidate_key(c) < runtime.candidate_key(best[c["root"]]):
            best[c["root"]] = c
    result = dict(schema=1, status="COMPLETE", file=old_result["file"], depth=depth,
                  source_candidate_count=len(candidates), rechecked_step_sat_candidates=len(selected),
                  source_reset_unsat_step_sat=sum(c["proof"]["reset"] == "UNSAT" for i, c in selected),
                  newly_proved_candidates=len(qualified), newly_proved_roots=len(best),
                  groups=[dict(reset_0=k[0], reset_1=k[1], image_2=k[2], count=v) for k, v in sorted(groups.items())],
                  overlapping_one_per_root_conservative_potential=sum(c["conservative_gain"] for c in best.values()),
                  potential_is_additive=False, measured_seq_build_gain=None, product_selection="NOT_RUN",
                  input_sha256=sha(source), frozen_evidence_unchanged=True, proof_queries=qstats,
                  wall_s=time.monotonic() - started)
    write_json(out / "result.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True, help="completed frozen pilot directory")
    parser.add_argument("--case", required=True, help="exact completed case subdirectory, e.g. 041_des_area")
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    try:
        result = recheck(args.run, args.run / args.case, args.solver.resolve(), args.out)
        print(json.dumps(result, sort_keys=True), flush=True)
        return 0
    except Exception as exc:
        result = dict(schema=1, status="TIMEOUT" if isinstance(exc, (TimeoutError, subprocess.TimeoutExpired)) else "ERROR",
                      file=args.case, error=str(exc), error_type=type(exc).__name__,
                      wall_s=time.monotonic() - start, measured_seq_build_gain=None,
                      newly_proved_candidates=None, timeout_is_zero=False)
        (args.out / "error.log").write_text(traceback.format_exc())
        write_json(args.out / "result.json", result)
        print(json.dumps(result, sort_keys=True), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
