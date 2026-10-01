#!/usr/bin/env python3
"""Extra-cost audit of complete certificates from an interrupted frozen attempt.

This never changes or completes the original attempt. It discovers no candidates.
Only an exact frozen query prefix is considered, and every retained triple is
rechecked in a fresh solver process before standalone replay and optional DSEC.
"""
from __future__ import annotations

import argparse
import csv
import io
import json
import math
from pathlib import Path
import shutil
import sys
import time
import traceback

from prototype import (Aiger, Config, Deadline, HERE, PACKAGE, Structure,
                       compile_graph, graph_recipe, normalize, recipe_eval,
                       require, run_queries, sha, signatures, witness, write_json)
from product import create_product


def read_complete_prefix(path, query_count):
    """A non-newline-terminated last row is incomplete, never a certificate."""
    raw = Path(path).read_bytes()
    text = raw.decode("ascii")
    lines = text.splitlines(keepends=True)
    require(bool(lines) and lines[0].rstrip("\r\n") == "query,result,conflicts,wall_s",
            "invalid solver CSV header")
    dropped = 0
    if len(lines) > 1 and not lines[-1].endswith("\n"):
        dropped = len(lines[-1].encode("ascii"))
        lines.pop()
    rows = []
    for line in lines[1:]:
        fields = next(csv.reader(io.StringIO(line)))
        require(len(fields) == 4, "malformed complete solver row")
        q, result, conflicts = map(int, fields[:3])
        wall = float(fields[3])
        require(q == len(rows) and q < query_count, "non-prefix or out-of-range query ID")
        require(result in (-1, 0, 1) and conflicts >= 0 and math.isfinite(wall) and wall >= 0,
                "invalid solver row value")
        rows.append(dict(query=q, result=result, conflicts=conflicts, wall_s=wall))
    return rows, dropped


def certificate_indices(rows):
    # Complete triplets only: free SAT, reset UNSAT, unrestricted image UNSAT.
    return [index for index in range(len(rows) // 3)
            if [r["result"] for r in rows[3 * index:3 * index + 3]] == [1, -1, -1]]


def source_check(provenance):
    expected = {"nonlinear_divisors/prototype.py": provenance["prototype_sha256"],
                **provenance["dependencies"]}
    checked = {}
    for relative, expected_hash in expected.items():
        # Only exactly packaged sources may be bound; traversal is not accepted.
        path = PACKAGE / relative
        require(path.resolve().is_relative_to(PACKAGE.resolve()), "source path escapes package")
        require(path.is_file() and sha(path) == expected_hash, f"frozen runtime source mismatch: {relative}")
        checked[relative] = expected_hash
    require("nonlinear_divisors/product.py" in checked, "missing product source identity")
    return checked


def audit(attempt, out, solver, abc=None, wall_seconds=120, dsec_seconds=120):
    start = time.monotonic()
    deadline = Deadline(wall_seconds)
    attempt = Path(attempt).resolve()
    require(attempt != out.resolve() and not out.resolve().is_relative_to(attempt),
            "audit output must be outside immutable original attempt")
    original_result = json.loads((attempt / "result.json").read_text())
    require(original_result["status"] == "TIMEOUT", "only original TIMEOUT attempts are eligible")
    provenance = json.loads((attempt / "provenance.json").read_text())
    source_hashes = source_check(provenance)
    require(sha(solver) == provenance["solver_sha256"], "fresh solver identity differs from original")
    config = Config(**provenance["config"])
    config.validate()
    rows = json.loads((PACKAGE / "cases.json").read_text())["cases"]
    case = next((row for row in rows if row["file"] == original_result["file"]), None)
    require(case is not None, "original case missing from packaged manifest")
    original_input = PACKAGE / case["first_seq_path"]
    require(case["first_seq_sha256"] == provenance["input_sha256"] == sha(original_input),
            "original input identity mismatch")
    required_files = ["result.json", "provenance.json", "candidates.unproved.json",
                      "query_order.json", "obligations.cnf", "obligations.queries", "obligations.results.csv"]
    evidence = {name: sha(attempt / name) for name in required_files}
    write_json(out / "audit_provenance.json", dict(
        schema=1, original_attempt=str(attempt), original_status="TIMEOUT",
        original_evidence_sha256=evidence, original_input_sha256=sha(original_input),
        frozen_runtime_sha256=source_hashes, audit_source_sha256=sha(__file__),
        solver_sha256=sha(solver), additional_budget_seconds=wall_seconds,
        separate_dsec_budget_seconds=dsec_seconds, original_config=provenance["config"],
        original_status_preserved=True, cohort_completion=False, same_budget_success=False))
    frozen_input = out / "audit_input.aig"
    shutil.copyfile(original_input, frozen_input)
    require(sha(frozen_input) == provenance["input_sha256"], "audit input copy mismatch")
    a = Aiger(frozen_input)
    s = Structure(a)
    g, base, step, reset = compile_graph(a)
    (free, image, initial), free_mask = signatures(g, [base, step, reset], config)
    seq_mask = (1 << (2 * config.lanes)) - 1
    seq = [image[i] | (initial[i] << config.lanes) for i in range(a.m + 1)]
    candidates = json.loads((attempt / "candidates.unproved.json").read_text())
    expected_order = json.loads((attempt / "query_order.json").read_text())
    actual_order, all_queries = [], []
    seen = set()
    for index, candidate in enumerate(candidates):
        deadline.remaining()
        root = candidate["root"]
        require(s.nci < root <= a.m and root in s.live, "invalid candidate root")
        recipe, output = normalize(s, root, candidate["recipe"], candidate["out"])
        require(recipe == candidate["recipe"] and output == candidate["out"] and bool(recipe),
                "frozen recipe is not a normalized Build")
        identity = root, tuple(recipe), output
        require(identity not in seen, "duplicate frozen candidate identity")
        seen.add(identity)
        exact_cost = s.cost(root, recipe, output)
        require(exact_cost["conservative_gain"] > 0 and
                all(candidate[key] == value for key, value in exact_cost.items()),
                "frozen candidate retention/cost mismatch")
        require(recipe_eval(recipe, output, seq, seq_mask) == seq[root], "frozen signature mismatch")
        candidate["free_witness"] = witness(a, candidate, free)
        for phase, mapping in (("free", base), ("reset", reset), ("step", step)):
            expression = graph_recipe(g, mapping, recipe, output)
            diff = g.xor(mapping[root], expression)
            actual_order.append(dict(query=len(all_queries), candidate=index, root=root,
                                     phase=phase, miter_literal=diff))
            all_queries.append([diff])
    require(actual_order == expected_order, "candidate-to-query mapping mismatch")
    g.cnf(out / "reconstructed_original.cnf")
    with (out / "reconstructed_original.queries").open("w") as stream:
        stream.write(f"{len(all_queries)}\n")
        for i, query in enumerate(all_queries):
            stream.write(f"{i} {len(query)} " + " ".join(map(str, query)) + "\n")
    require(sha(out / "reconstructed_original.cnf") == evidence["obligations.cnf"],
            "frozen CNF does not match original graph and recipes")
    require(sha(out / "reconstructed_original.queries") == evidence["obligations.queries"],
            "frozen queries do not match original recipes")
    prefix, dropped_bytes = read_complete_prefix(attempt / "obligations.results.csv", len(all_queries))
    indices = certificate_indices(prefix)
    write_json(out / "prefix_validation.json", dict(
        status="PASS", complete_query_rows=len(prefix), total_query_rows=len(all_queries),
        incomplete_tail_bytes=dropped_bytes, complete_triples=len(prefix) // 3,
        complete_positive_triples=len(indices), candidate_indices=indices,
        candidate_order_and_full_cnf_byte_identity=True,
        all_candidate_costs_and_sampled_witnesses_replayed=True))
    recheck_queries = [all_queries[3 * i + phase] for i in indices for phase in range(3)]
    answers, query_stats = run_queries(g, recheck_queries, out, solver, deadline)
    rechecked = []
    status = {-1: "UNSAT", 0: "UNKNOWN", 1: "SAT"}
    for position, index in enumerate(indices):
        c = candidates[index]
        fs, rs, ss = answers[3 * position:3 * position + 3]
        require(fs != -1, "fresh UNSAT contradicts original free witness")
        require(rs != 1 and ss != 1, "fresh SAT contradicts original UNSAT certificate")
        c["proof"] = dict(free=status[fs], reset=status[rs], step=status[ss],
                          free_witness_replayed=True,
                          sequential_relation="PROVED_RESET_IMAGE" if rs == ss == -1 else "NOT_PROVED",
                          original_candidate_index=index,
                          extra_cost_fresh_solver_recheck=True,
                          production_seq_proof="NOT_RUN", commit="NOT_RUN", dsec="NOT_RUN",
                          exact_selected_set_gain=None, main_metric_eligible=False,
                          native_recipe_novelty="NOT_CHECKED")
        c["qualified_offline_opportunity"] = fs == 1 and rs == ss == -1
        rechecked.append(c)
    write_json(out / "rechecked_candidates.json", rechecked)
    qualified = [c for c in rechecked if c["qualified_offline_opportunity"]]
    product = create_product(frozen_input, qualified, out, abc, dsec_seconds,
                             expected_input_sha256=provenance["input_sha256"], deadline=deadline)
    require(all(sha(attempt / name) == value for name, value in evidence.items()),
            "original attempt evidence changed during audit")
    result = dict(schema=1, status="PARTIAL_CERTIFICATE_AUDIT_COMPLETE",
                  original_attempt_status="TIMEOUT", original_attempt_unchanged=True,
                  cohort_completion=False, same_budget_success=False,
                  candidate_discovery_extended=False, file=case["file"],
                  loaded_and=case["loaded_AND"], complete_prefix_rows=len(prefix),
                  original_query_rows=len(all_queries), original_complete_proved_triples=len(indices),
                  fresh_recheck_qualified=len(qualified), fresh_recheck_queries=query_stats,
                  product=product, extra_total_wall_s=time.monotonic() - start,
                  extra_non_dsec_wall_s=(time.monotonic() - start - sum(
                      product[key].get("wall_s", 0) for key in ("baseline_dsec", "independent_dsec"))))
    write_json(out / "audit_result.json", result)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--attempt", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    p.add_argument("--solver", required=True, type=Path)
    p.add_argument("--abc", type=Path)
    p.add_argument("--wall-seconds", type=float, default=120.0)
    p.add_argument("--dsec-seconds", type=float, default=120.0)
    a = p.parse_args()
    if a.wall_seconds <= 0 or a.dsec_seconds <= 0:
        p.error("budgets must be positive")
    if a.out.resolve() == a.attempt.resolve() or a.out.resolve().is_relative_to(a.attempt.resolve()):
        p.error("audit output must be outside original attempt")
    a.out.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    try:
        result = audit(a.attempt, a.out, a.solver, a.abc, a.wall_seconds, a.dsec_seconds)
        print(json.dumps(result, sort_keys=True))
        return 0
    except BaseException as error:
        import subprocess
        timeout = isinstance(error, (TimeoutError, subprocess.TimeoutExpired))
        result = dict(status="PARTIAL_AUDIT_TIMEOUT" if timeout else "PARTIAL_AUDIT_ERROR",
                      error=repr(error), original_attempt_status="TIMEOUT", cohort_completion=False,
                      same_budget_success=False, validated_standalone_noncomb_build_gain=None,
                      extra_wall_s=time.monotonic() - start)
        write_json(a.out / "audit_result.json", result)
        (a.out / "error.log").write_text(traceback.format_exc())
        print(json.dumps(result, sort_keys=True), file=sys.stderr)
        return 124 if timeout else 1


if __name__ == "__main__":
    raise SystemExit(main())
