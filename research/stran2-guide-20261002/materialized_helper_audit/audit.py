#!/usr/bin/env python3
"""Fixed-cohort ordinary-scorr proof comparator; never substitute original roots.

Inputs are the selected recipes of frozen anytime-v2 checkpoints. Auxiliary
logic is observable through paired POs. Original gates, POs, RI functions and
reset are copied literally. This experiment does not measure implementation QoR.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import signal
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
CASES = ("005_b03", "034_b20_opt", "060_wb_dma")


def digest_json(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def load_runtime(source):
    sys.path.insert(0, str(source / "nonlinear_divisors"))
    import prototype as p
    import product as prod
    import anytime as at
    return p, prod, at


def materialize(a, selected, p):
    # Do not rebuild/substitute/cleanup the original. Source IDs are identity.
    g = p.Graph()
    g.gates = [None] * (a.ni + a.nl + 1) + list(a.gates)
    g.hash = {}
    for node, gate in enumerate(g.gates):
        if gate is not None:
            g.hash.setdefault(tuple(sorted(gate)), 2 * node)
    mapping = [2 * node for node in range(a.m + 1)]
    outputs = list(a.outputs)
    pairs = []
    for index, candidate in enumerate(selected):
        root = candidate["root"]
        p.require(a.ni + a.nl < root <= a.m, "root is not an original AND")
        p.require(all(0 < n < root for n in p.external_nodes(candidate["recipe"], candidate["out"])),
                  "non-original or cyclic recipe divisor")
        before = len(g.gates)
        helper = p.graph_recipe(g, mapping, candidate["recipe"], candidate["out"])
        pair_index = len(outputs)
        outputs += [2 * root, helper]
        pairs.append(dict(index=index, root=root, recipe=candidate["recipe"], out=candidate["out"],
                          candidate_sha256=digest_json(candidate),
                          free_witness_sha256=digest_json(candidate["free_witness"]),
                          root_po_index=pair_index, helper_po_index=pair_index + 1,
                          root_literal=2 * root, helper_literal=helper,
                          appended_nodes=list(range(before, len(g.gates)))))
    gates = g.gates[a.ni + a.nl + 1:]
    p.require(gates[:a.na] == a.gates, "original graph changed")
    live, todo = set(), [x // 2 for x in outputs + a.latches]
    while todo:
        node = todo.pop()
        if node in live:
            continue
        live.add(node)
        if g.gates[node] is not None:
            todo.extend(x // 2 for x in g.gates[node])
    for pair in pairs:
        p.require(pair["helper_literal"] // 2 in live, "helper was not retained")
        pair["live_appended_nodes"] = [n for n in pair["appended_nodes"] if n in live]
    return dict(ni=a.ni, nl=a.nl, outputs=outputs, latches=list(a.latches), gates=gates), pairs


def audit_materialization(original, augmented, selected, pairs, p):
    p.require(original.ni == augmented.ni and original.nl == augmented.nl, "CI/register interface changed")
    p.require(original.initial == augmented.initial and original.latches == augmented.latches,
              "transition or reset changed")
    p.require(augmented.gates[:original.na] == original.gates and
              augmented.outputs[:original.no] == original.outputs, "original CO logic changed")
    rng = random.Random(2026100207)
    vectors = [(c["free_witness"]["inputs"], c["free_witness"]["state"]) for c in selected]
    vectors += [([rng.randrange(2) for _ in range(original.ni)],
                 [rng.randrange(2) for _ in range(original.nl)]) for _ in range(128)]
    for inputs, state in vectors:
        old_po, old_ri, values = original.step(inputs, state)
        new_po, new_ri, _ = augmented.step(inputs, state)
        p.require(new_po[:original.no] == old_po and new_ri == old_ri, "original PO/RI replay failed")
        for candidate, pair in zip(selected, pairs):
            expected = p.recipe_eval(candidate["recipe"], candidate["out"], values)
            p.require(new_po[pair["root_po_index"]] == values[candidate["root"]] and
                      new_po[pair["helper_po_index"]] == expected, "root/helper replay failed")
    for candidate, pair in zip(selected, pairs):
        witness = candidate["free_witness"]
        po, _, values = augmented.step(witness["inputs"], witness["state"])
        p.require(po[pair["root_po_index"]] != po[pair["helper_po_index"]], "free witness no longer distinguishes")
        p.require(po[pair["root_po_index"]] == witness["root"] and
                  po[pair["helper_po_index"]] == witness["replacement"], "witness identity changed")
    return dict(status="PASS", random_free_vectors=128, free_witnesses=len(selected),
                exact_original_gates_po_ri_reset_preserved=True)


def command_run(abc, command, log, budget):
    start = time.monotonic()
    result = dict(command=command, timeout_seconds=budget, status="NOT_RUN")
    with log.open("w") as handle:
        process = subprocess.Popen([str(abc), "-c", command], stdout=handle,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=budget)
            result.update(exit_code=code, status="EXIT" if code == 0 else "ERROR")
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            result.update(exit_code=process.returncode, status="TIMEOUT")
    result["wall_s"] = time.monotonic() - start
    result["log_sha256"] = hashlib.sha256(log.read_bytes()).hexdigest()
    text = log.read_text(errors="replace")
    if re.search(r"Assertion.*failed", text, re.S):
        result["status"] = "ASSERTION"
    elif re.search(r"(^|\n)(Error:|Cannot open|usage:)", text):
        result["status"] = "COMMAND_ERROR"
    return result


def inspect_pairs(graph, pairs):
    return [dict(index=p["index"], root=p["root"],
                 root_co_literal=graph.outputs[p["root_po_index"]],
                 helper_co_literal=graph.outputs[p["helper_po_index"]],
                 status="MERGED" if graph.outputs[p["root_po_index"]] == graph.outputs[p["helper_po_index"]]
                        else "NOT_MERGED") for p in pairs]


def run_case(name, args, p, prod, at):
    start = time.monotonic()
    out = args.out / name
    out.mkdir()
    source_case = args.run / name
    source_result = json.loads((source_case / "result.json").read_text())
    job = json.loads((source_case / "job.json").read_text())
    input_path = args.inputs / (name + ".aig")
    input_hash = p.sha(input_path)
    p.require(input_hash == source_result["input_sha256"] == job["case"]["input_sha256"], "input hash mismatch")
    selected_name = Path(source_result["selected_checkpoint"]["directory"]).name
    notice = next(x for x in source_result["driver"]["observed_checkpoints"] if x["directory"] == selected_name)
    checkpoint, metadata = at.verify_checkpoint(source_case, notice, input_hash)
    selected = json.loads((checkpoint / "selection.json").read_text())["selected"]
    p.write_json(out / "selected.json", selected)
    a = p.Aiger(input_path)
    graph, pairs = materialize(a, selected, p)
    augmented = out / "augmented.aig"
    prod.write_aig(augmented, graph)
    aug = p.Aiger(augmented)
    validation = audit_materialization(a, aug, selected, pairs, p)
    p.require(all(x["status"] == "NOT_MERGED" for x in inspect_pairs(aug, pairs)), "preexisting structural pair equality")
    p.write_json(out / "pairs.json", pairs)
    result = dict(schema=1, case=name, input_sha256=input_hash,
                  input_graph_sha256=a.graph_sha256, augmented_sha256=p.sha(augmented),
                  augmented_graph_sha256=aug.graph_sha256,
                  source_result_sha256=p.sha(source_case / "result.json"),
                  checkpoint=str(checkpoint), checkpoint_sha256=p.sha(checkpoint / "checkpoint.json"),
                  source_selection_sha256=p.sha(checkpoint / "selection.json"),
                  selected_count=len(selected), selected_snapshot_sha256=p.sha(out / "selected.json"),
                  materialization_validation=validation, pairs=pairs,
                  original_counts=dict(pi=a.ni, registers=a.nl, po=a.no, ands=a.na),
                  augmented_counts=dict(pi=aug.ni, registers=aug.nl, po=aug.no, ands=aug.na),
                  scorr_rounds=[], scorr_status="NOT_RUN", dsec=dict(status="NOT_RUN"),
                  proof_evidence_count=0, native_qor_claim=False,
                  nonmerge_interpretation="INCONCLUSIVE_NOT_DISPROOF")
    p.write_json(out / "result.json", result)
    current, prior = augmented, aug
    sweep_start = time.monotonic()
    while True:
        remaining = args.scorr_seconds - (time.monotonic() - sweep_start)
        if remaining <= 0:
            result["scorr_status"] = "BUDGET_EXHAUSTED"
            break
        number = len(result["scorr_rounds"]) + 1
        after = out / f"round_{number:03d}.aig"
        loaded = out / f"loaded_{number:03d}.aig"
        command = f"&r {current}; &w {loaded}; &scorr -F 1 -C 1000 -v; &w {after}"
        run = command_run(args.abc, command, out / f"round_{number:03d}.log", remaining)
        run["round"] = number
        if run["status"] != "EXIT" or not after.exists():
            run["status"] = run["status"] if run["status"] != "EXIT" else "MISSING_OUTPUT"
            result["scorr_rounds"].append(run)
            result["scorr_status"] = run["status"]
            break
        final = p.Aiger(after)
        loaded_graph = p.Aiger(loaded)
        p.require(final.ni == a.ni and final.no == aug.no, "scorr PO/PI interface changed")
        loaded_pairs = inspect_pairs(loaded_graph, pairs)
        pair_result = inspect_pairs(final, pairs)
        run.update(before_sha256=p.sha(current), loaded_sha256=p.sha(loaded), after_sha256=p.sha(after),
                   loaded_graph_sha256=loaded_graph.graph_sha256, after_graph_sha256=final.graph_sha256,
                   loaded_pairs=loaded_pairs, pairs=pair_result,
                   merged=sum(x["status"] == "MERGED" for x in pair_result),
                   exact_graph_fixedpoint=loaded_graph.graph_sha256 == final.graph_sha256)
        result["scorr_rounds"].append(run)
        current, prior = after, final
        if run["merged"] == len(selected):
            result["scorr_status"] = "ALL_PAIRS_MERGED"
            break
        if run["exact_graph_fixedpoint"]:
            result["scorr_status"] = "EXACT_GRAPH_FIXEDPOINT"
            break
    result["scorr_total_wall_s"] = time.monotonic() - sweep_start
    if current != augmented:
        result["final_sha256"] = p.sha(current)
        result["final_graph_sha256"] = prior.graph_sha256
        result["final_graph"] = current.name
        result["final_pairs"] = inspect_pairs(prior, pairs)
        result["dsec"] = prod.dsec(args.abc, augmented, current, out, args.dsec_seconds, "augmented_dsec")
        if result["dsec"]["status"] == "PASS":
            result["proof_evidence_count"] = sum(x["status"] == "MERGED" for x in result["final_pairs"])
        for pair in result["final_pairs"]:
            pair["native_proof_evidence"] = pair["status"] == "MERGED" and result["dsec"]["status"] == "PASS"
    result["total_wall_s"] = time.monotonic() - start
    p.write_json(out / "result.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--abc", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--scorr-seconds", type=float, default=120)
    parser.add_argument("--dsec-seconds", type=float, default=120)
    args = parser.parse_args()
    for key in ("run", "inputs", "abc", "out"):
        setattr(args, key, getattr(args, key).resolve())
        if not re.fullmatch(r"[A-Za-z0-9_./+:-]+", str(getattr(args, key))):
            parser.error("unsupported path characters")
    if not 0 < args.scorr_seconds <= 120 or not 0 < args.dsec_seconds <= 120:
        parser.error("audit budgets must be in (0,120]")
    args.out.mkdir(parents=True, exist_ok=False)
    p, prod, at = load_runtime(args.run / "source")
    plan = json.loads((args.run / "plan.json").read_text())
    source_hashes = plan["runtime_source_hashes"]
    p.require(all(p.sha(args.run / "source" / file) == value for file, value in source_hashes.items()), "frozen runtime hash changed")
    manifest = dict(schema=1, fixed_cases=list(CASES), source_run=str(args.run), source_hashes=source_hashes,
                    audit_script_sha256=p.sha(Path(__file__)), abc_sha256=p.sha(args.abc),
                    scorr_command="&scorr -F 1 -C 1000 -v", scorr_total_budget_per_case=args.scorr_seconds,
                    dsec_separate_budget_per_case=args.dsec_seconds,
                    stopping_rule="Stop when all selected pairs merge; otherwise repeat identical command on its output until exact loaded graph fixedpoint or shared 120s budget",
                    interpretation="Tests ordinary scorr acquisition of supplied relations, not expression discovery, new proof power, area, or native QoR")
    p.write_json(args.out / "plan.json", manifest)
    command_run(args.abc, "&scorr -h", args.out / "scorr_help.log", 10)
    results = []
    for case in CASES:
        try:
            result = run_case(case, args, p, prod, at)
        except Exception as error:
            path = args.out / case
            path.mkdir(exist_ok=True)
            (path / "error.log").write_text(traceback.format_exc())
            result = dict(case=case, status="ERROR", error=repr(error))
            p.write_json(path / "error.json", result)
        results.append(result)
        print(json.dumps({k: result.get(k) for k in ("case", "scorr_status", "selected_count", "proof_evidence_count", "scorr_total_wall_s", "dsec", "error")}), flush=True)
        p.write_json(args.out / "results.json", results)
    p.require(p.sha(args.abc) == manifest["abc_sha256"], "ABC binary changed during run")
    p.require(all(p.sha(args.run / "source" / file) == value for file, value in source_hashes.items()), "source changed during run")
    p.write_json(args.out / "summary.json", dict(cases=len(results), selected=sum(x.get("selected_count", 0) for x in results),
                native_proof_evidence=sum(x.get("proof_evidence_count", 0) for x in results),
                errors=sum("error" in x for x in results), dsec_pass=sum(x.get("dsec", {}).get("status") == "PASS" for x in results),
                nonmerge_is_disproof=False, new_area_or_native_qor_claim=False))


if __name__ == "__main__":
    main()
