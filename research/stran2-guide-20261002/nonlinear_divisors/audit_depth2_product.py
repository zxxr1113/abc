#!/usr/bin/env python3
"""Bind saved depth-two certificates to explicit standalone product/replays.

No candidate discovery; original shallow SAT is preserved. All evidence is
reconstructed/rechecked before an additional typed certificate is attached.
"""
from __future__ import annotations

import argparse
import copy
import csv
import json
from pathlib import Path
import shutil
import sys
import time
import traceback

import prototype as runtime
import deeper_image
from audit_partial import source_check
from product_depth2 import create_certified_product, candidate_certificate_sha


def audit(source_case, proof_dir, out, solver, abc, seconds=120, dsec_seconds=120):
    started = time.monotonic()
    deadline = runtime.Deadline(seconds)
    source_case, proof_dir, out = map(lambda p: Path(p).resolve(), (source_case, proof_dir, out))
    runtime.require(not out.is_relative_to(source_case) and not out.is_relative_to(proof_dir),
                    "new output must be outside original proof/case")
    package, source, candidates, original_result, bound = deeper_image.verify_frozen(
        source_case.parent, source_case, solver)
    source_provenance = json.loads((source_case / "provenance.json").read_text())
    frozen_current_sources = source_check(source_provenance)
    provenance = json.loads((proof_dir / "provenance.json").read_text())
    input_sha256 = provenance["input_sha256"]
    result = json.loads((proof_dir / "result.json").read_text())
    runtime.require(result["status"] == "COMPLETE" and result["depth"] == provenance["depth"] == 2,
                    "only complete depth-two proof files accepted")
    runtime.require(provenance["source_case"] == str(source_case) and
                    provenance["input_sha256"] == result["input_sha256"] == runtime.sha(source),
                    "depth-two source input mismatch")
    deeper_image.assert_unchanged(provenance["source_identity"])
    runtime.require(runtime.sha(deeper_image.__file__) == provenance["rechecker_sha256"] ==
                    runtime.sha(proof_dir / "rechecker.source.py"), "depth-two checker source changed")
    records = json.loads((proof_dir / "candidates.rechecked.json").read_text())
    qualified_records = json.loads((proof_dir / "qualified.json").read_text())
    indexed = [(i, c) for i, c in enumerate(candidates) if c["proof"]["step"] == "SAT"]
    runtime.require([r["source_candidate_index"] for r in records] == [i for i, c in indexed],
                    "depth-two recheck order mismatch")
    with (proof_dir / "obligations.results.csv").open() as stream:
        saved_rows = list(csv.DictReader(stream))
    runtime.require(len(saved_rows) == 3 * len(indexed), "incomplete saved depth-two solver output")
    proof_evidence = {}
    for name, field in (("obligations.cnf", "cnf_sha256"), ("obligations.queries", "queries_sha256"),
                        ("obligations.results.csv", "results_sha256")):
        runtime.require(runtime.sha(proof_dir / name) == result["proof_queries"][field],
                        "saved depth-two proof hash mismatch")
    for name in ("provenance.json", "result.json", "candidates.rechecked.json", "qualified.json",
                 "query_order.json", "obligations.cnf", "obligations.queries", "obligations.results.csv"):
        proof_evidence[str(proof_dir / name)] = runtime.sha(proof_dir / name)
    a = runtime.Aiger(source)
    s = runtime.Structure(a)
    for pos, ((index, c), record) in enumerate(zip(indexed, records)):
        runtime.require(c == record["candidate"] and record["source_candidate_sha256"] == deeper_image.json_sha(c),
                        "candidate differs from depth-two certificate identity")
        answers = []
        for phase in range(3):
            row = saved_rows[3 * pos + phase]
            runtime.require(int(row["query"]) == 3 * pos + phase and int(row["result"]) in (-1, 0, 1),
                            "saved depth-two query ordering/status mismatch")
            answers.append(deeper_image.STATUS[int(row["result"])])
        recheck = record["recheck"]
        runtime.require(recheck["depth"] == 2 and recheck["reset_prefix"] == answers[:2] and
                        recheck["unrestricted_image"] == answers[2] and
                        recheck["complete_sufficient_proof"] == all(x == "UNSAT" for x in answers) and
                        record["qualified_two_step_opportunity"] == all(x == "UNSAT" for x in answers),
                        "saved depth-two statuses contradict raw query results")
        w = c["free_witness"]
        runtime.require(c["proof"]["free"] == "SAT" and c["proof"]["free_witness_replayed"] and
                        w["kind"] == "free_PI_RO" and w["replay"] == "PASS" and
                        all(type(v) is int and v in (0, 1) for v in w["inputs"] + w["state"]),
                        "missing or malformed free witness")
        values = a.step(w["inputs"], w["state"])[2]
        replacement = runtime.recipe_eval(c["recipe"], c["out"], values)
        runtime.require(values[c["root"]] == w["root"] != w["replacement"] == replacement,
                        "depth-two candidate free witness mismatch")
        cost = s.cost(c["root"], c["recipe"], c["out"])
        runtime.require(all(c[key] == value for key, value in cost.items()), "candidate cost changed")
    runtime.require(qualified_records == [r for r in records if r["qualified_two_step_opportunity"]],
                    "qualified records do not match exact proved subset")
    g, queries, order, _ = deeper_image.make_queries(a, indexed, 2, runtime, deadline)
    runtime.require(order == json.loads((proof_dir / "query_order.json").read_text()),
                    "regenerated depth-two query order differs")
    recheck_out = out / "fresh_depth2"
    recheck_out.mkdir()
    runtime.write_json(recheck_out / "query_order.json", order)
    answers, query_stats = runtime.run_queries(g, queries, recheck_out, solver, deadline)
    runtime.require(query_stats["cnf_sha256"] == result["proof_queries"]["cnf_sha256"] and
                    query_stats["queries_sha256"] == result["proof_queries"]["queries_sha256"],
                    "regenerated depth-two CNF/queries differ")
    new = []
    for pos, ((index, c), record) in enumerate(zip(indexed, records)):
        if not record["qualified_two_step_opportunity"]:
            continue
        fresh = answers[3 * pos:3 * pos + 3]
        runtime.require(1 not in fresh, "fresh SAT contradicts saved depth-two UNSAT")
        if fresh != [-1, -1, -1]:
            continue
        candidate = copy.deepcopy(c)
        candidate["depth2_certificate"] = dict(
            schema=1, kind="RESET_PREFIX_IMAGE", depth=2,
            input_sha256=input_sha256, candidate_sha256=candidate_certificate_sha(c),
            reset_prefix=["UNSAT", "UNSAT"], unrestricted_image="UNSAT", free_witness_replayed=True,
            fresh_recheck="PASS", evidence_sha256=dict(cnf=query_stats["cnf_sha256"],
                queries=query_stats["queries_sha256"], results=query_stats["results_sha256"],
                query_order=runtime.sha(recheck_out / "query_order.json")))
        runtime.require(candidate["proof"]["step"] == "SAT", "original shallow status changed")
        new.append(candidate)
    old = [c for c in candidates if c["qualified_offline_opportunity"]]
    product_sources = {name: runtime.sha(Path(__file__).parent / name) for name in (
        "prototype.py", "product.py", "product_depth2.py", "deeper_image.py", "audit_partial.py", "audit_depth2_product.py")}
    runtime.write_json(out / "audit_provenance.json", dict(
        original_case=str(source_case), original_case_status="COMPLETE", original_proof_statuses_preserved=True,
        original_depth2_proof=str(proof_dir), input_sha256=input_sha256,
        frozen_source_evidence=bound, depth2_evidence=proof_evidence,
        auditor_sources=product_sources, bound_current_runtime_sources=frozen_current_sources, extra_budget_seconds=seconds,
        per_product_dsec_seconds=dsec_seconds, candidate_search="NOT_RERUN"))
    (out / "source").mkdir()
    for name in product_sources:
        shutil.copyfile(Path(__file__).parent / name, out / "source" / name)
    runtime.write_json(out / "newly_certified_candidates.json", new)
    products = {}

    def build(name, cs):
        dest = out / name
        dest.mkdir()
        products[name] = create_certified_product(source, cs, dest, abc, dsec_seconds,
                            expected_input_sha256=input_sha256, deadline=deadline)
        # Independent DSEC has a separate budget, including in this multi-product audit.
        deadline.end += sum(products[name][key].get("wall_s", 0) for key in ("baseline_dsec", "independent_dsec"))

    build("depth1_reference", old)
    build("depth2_only", new)
    build("union", old + new)
    selected_union = json.loads((out / "union/selection.json").read_text())["selected"]
    fixed_old_subset = [c for c in selected_union if "depth2_certificate" not in c]
    build("union_without_depth2", fixed_old_subset)
    replayed_subset = json.loads((out / "union_without_depth2/selection.json").read_text())["selected"]
    identity = lambda c: (c["root"], tuple(c["recipe"]), c["out"])
    runtime.require(sorted(map(identity, replayed_subset)) == sorted(map(identity, fixed_old_subset)),
                    "counterfactual selection changed the fixed old subset")
    marginal = products["union_without_depth2"]["product_and"] - products["union"]["product_and"]
    validated = all(p["validated_standalone_noncomb_build_gain"] is not None for p in products.values())
    runtime.require(source_check(source_provenance) == frozen_current_sources, "runtime sources changed")
    deeper_image.assert_unchanged(bound)
    deeper_image.assert_unchanged(proof_evidence)
    runtime.require(all(runtime.sha(Path(__file__).parent / name) == value for name, value in product_sources.items()),
                    "product auditor source changed")
    audit_result = dict(schema=1, status="DEPTH2_PRODUCT_AUDIT_COMPLETE", source_statuses_unchanged=True,
        candidate_search="NOT_RERUN", newly_certified_candidates=len(new),
        extra_query_stats=query_stats, products=products,
        union_gain_minus_depth1_reference_gain=products["union"]["exact_same_selected_set_build_gain"] -
            products["depth1_reference"]["exact_same_selected_set_build_gain"],
        exact_depth2_same_selected_set_marginal=marginal,
        fixed_subset_identity_verified=True,
        validated_depth2_same_selected_set_marginal=marginal if validated else None,
        extra_total_wall_s=time.monotonic() - started, production_integration="NOT_RUN",
        native_recipe_novelty="NOT_CHECKED", original_120s_cohort_result_unchanged=True)
    runtime.write_json(out / "audit_result.json", audit_result)
    return audit_result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source-case", required=True, type=Path)
    p.add_argument("--proof-dir", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    p.add_argument("--solver", required=True, type=Path)
    p.add_argument("--abc", required=True, type=Path)
    p.add_argument("--wall-seconds", type=float, default=120.0)
    p.add_argument("--dsec-seconds", type=float, default=120.0)
    args = p.parse_args()
    if args.wall_seconds <= 0 or args.dsec_seconds <= 0:
        p.error("budgets must be positive")
    if args.out.resolve().is_relative_to(args.source_case.resolve()) or args.out.resolve().is_relative_to(args.proof_dir.resolve()):
        p.error("new output must be outside original case/proof")
    args.out.mkdir(parents=True, exist_ok=False)
    try:
        result = audit(args.source_case, args.proof_dir, args.out, args.solver, args.abc,
                       args.wall_seconds, args.dsec_seconds)
        print(json.dumps(result, sort_keys=True))
        return 0
    except BaseException as error:
        runtime.write_json(args.out / "audit_result.json", dict(status="DEPTH2_PRODUCT_AUDIT_ERROR", error=repr(error)))
        (args.out / "error.log").write_text(traceback.format_exc())
        raise


if __name__ == "__main__":
    raise SystemExit(main())
