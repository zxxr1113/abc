#!/usr/bin/env python3
"""Conservative simultaneous selection, exact reconstruction, and optional DSEC.

Standalone research products, never production &stran2 commits. Candidate proof
always refers to the immutable input, and every replacement external ID is below
its root. Reconstruction substitutes whole original roots in topological order.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import time

from prototype import (Aiger, Graph, Structure, candidate_key, external_nodes,
                       graph_recipe, require, sha, write_json)
from guide import dsec_answer


def select(s, candidates, deadline=None):
    """Disjoint deletions and no deletion of another recipe's dependencies."""
    selected, rejected = [], []
    removed, retained, roots = set(), set(), set()
    for candidate in sorted(candidates, key=candidate_key):
        if deadline is not None:
            deadline.remaining()
        root = candidate["root"]
        current = s.cost(root, candidate["recipe"], candidate["out"])
        require(current["conservative_gain"] == candidate["conservative_gain"], "stale candidate gain")
        deleting = set(current["removable_nodes"])
        keeping = s.tfi(external_nodes(candidate["recipe"], candidate["out"]))
        reason = None
        if root in roots:
            reason = "same_root"
        elif deleting & removed:
            reason = "overlapping_deletion"
        elif deleting & retained or keeping & removed:
            reason = "divisor_dependency_conflict"
        if reason:
            rejected.append(dict(root=root, reason=reason, recipe=candidate["recipe"], out=candidate["out"]))
            continue
        selected.append(candidate)
        roots.add(root)
        removed |= deleting
        retained |= keeping
    return sorted(selected, key=lambda c: c["root"]), rejected


def rebuild(a, selected, deadline=None):
    replacements = {c["root"]: c for c in selected}
    require(len(replacements) == len(selected), "duplicate replacement root")
    g = Graph()
    mapped = [0] + [g.pi() for _ in range(a.ni + a.nl)]
    realization = []
    for root, (x, y) in enumerate(a.gates, a.ni + a.nl + 1):
        if deadline is not None and root % 256 == 0:
            deadline.remaining()
        if root in replacements:
            c = replacements[root]
            require(all(0 < d < root for d in external_nodes(c["recipe"], c["out"])), "cyclic replacement")
            before = len(g.gates)
            value = graph_recipe(g, mapped, c["recipe"], c["out"])
            realization.append(dict(root=root, actually_created_gates=len(g.gates) - before,
                                    output_literal=value, output_is_new=before <= value // 2 < len(g.gates),
                                    created_nodes=list(range(before, len(g.gates)))))
        else:
            value = g.land(mapped[x // 2] ^ (x & 1), mapped[y // 2] ^ (y & 1))
        mapped.append(value)
    outputs = [mapped[x // 2] ^ (x & 1) for x in a.outputs]
    latches = [mapped[x // 2] ^ (x & 1) for x in a.latches]
    live, todo = set(), [lit // 2 for lit in outputs + latches]
    while todo:
        node = todo.pop()
        if node in live:
            continue
        live.add(node)
        if g.gates[node] is not None:
            todo.extend(lit // 2 for lit in g.gates[node])
    nci = a.ni + a.nl
    old_to_new = {node: node for node in range(nci + 1)}
    old_to_new.update({old: nci + 1 + index for index, old in enumerate(
        node for node in range(nci + 1, len(g.gates)) if node in live)})

    def lit(value):
        return 2 * old_to_new[value // 2] + (value & 1)

    gates = [tuple(lit(x) for x in g.gates[node]) for node in range(nci + 1, len(g.gates)) if node in live]
    for row in realization:
        row["output_is_live"] = row["output_literal"] // 2 in live
        row["live_created_gates"] = sum(node in live for node in row["created_nodes"])
    return dict(ni=a.ni, nl=a.nl, outputs=[lit(x) for x in outputs],
                latches=[lit(x) for x in latches], gates=gates,
                realization=realization)


def write_aig(path, graph):
    ni, nl, gates = graph["ni"], graph["nl"], graph["gates"]
    data = bytearray(f'aig {ni + nl + len(gates)} {ni} {nl} {len(graph["outputs"])} {len(gates)}\n'.encode())
    for value in graph["latches"] + graph["outputs"]:
        data.extend(f"{value}\n".encode())

    def varint(value):
        require(value >= 0, "non-topological emitted AIG")
        while value >= 128:
            data.append((value & 127) | 128)
            value >>= 7
        data.append(value)

    for node, gate in enumerate(gates, ni + nl + 1):
        hi, lo = sorted(gate, reverse=True)
        require(hi < 2 * node, "emitted cycle")
        varint(2 * node - hi)
        varint(hi - lo)
    data.extend(b"c\nnonlinear_divisors standalone research product\n")
    Path(path).write_bytes(data)
    parsed = Aiger(path)
    require(parsed.na == len(gates) and parsed.ni == ni and parsed.nl == nl,
            "emitted AIG failed independent parse")
    return sha(path)


def dsec(abc, original, product, out, seconds=120, tag="dsec"):
    logpath = out / (tag + ".log")
    """Retain independent child exit/status/log; exit zero alone is not PASS."""
    # ABC parser does not support arbitrary command-shell metacharacters in paths.
    for path in (original, product):
        require(re.fullmatch(r"[A-Za-z0-9_./+:-]+", str(Path(path).resolve())) is not None,
                "DSEC path contains unsupported characters")
    command = f"dsec {Path(original).resolve()} {Path(product).resolve()}"
    start = time.monotonic()
    result = dict(status="NOT_RUN", command=command, abc=str(Path(abc).resolve()),
                  abc_sha256=sha(abc), timeout_seconds=seconds)
    try:
        with logpath.open("w") as log:
            p = subprocess.run([str(Path(abc).resolve()), "-c", command], stdout=log,
                               stderr=subprocess.STDOUT, timeout=seconds, check=False)
        result["exit_code"] = p.returncode
        text = logpath.read_text(errors="replace")
        process_status = "exit" if p.returncode == 0 else "error"
        if re.search(r"Assertion.*failed", text, re.S):
            process_status = "assertion"
        status = dsec_answer(dict(status=process_status), text).upper().replace("-", "_")
        result["status"] = status
    except subprocess.TimeoutExpired:
        result["status"] = "TIMEOUT"
    result["wall_s"] = time.monotonic() - start
    result["log_sha256"] = sha(logpath)
    return result


def create_product(input_path, candidates, out, abc=None, dsec_seconds=120,
                   expected_input_sha256=None, deadline=None):
    actual_input_sha256 = sha(input_path)
    if expected_input_sha256 is not None:
        require(actual_input_sha256 == expected_input_sha256, "input changed after candidate proof")
    a = Aiger(input_path)
    require(sha(input_path) == actual_input_sha256, "input changed during parsing")
    if deadline is not None:
        deadline.remaining()
    s = Structure(a)
    for c in candidates:
        p = c["proof"]
        require(c["qualified_offline_opportunity"] and p["free"] == "SAT" and
                p["reset"] == p["step"] == "UNSAT" and p["free_witness_replayed"],
                "unproved candidate cannot enter product")
    chosen, rejected = select(s, candidates, deadline)
    product = rebuild(a, chosen, deadline)
    # Shared structural hashes can demote an otherwise fresh recipe to Direct.
    # Exclude these rather than crediting them as new Build.
    demoted = {row["root"] for row in product["realization"] if not row["output_is_new"] or row["live_created_gates"] == 0}
    if demoted:
        rejected.extend(dict(root=root, reason="direct_after_selected_set_hash") for root in sorted(demoted))
        chosen = [c for c in chosen if c["root"] not in demoted]
        product = rebuild(a, chosen, deadline)
    require(all(row["output_is_new"] and row["live_created_gates"] > 0 and row["output_is_live"]
                for row in product["realization"]), "selected Build not realized/live")
    baseline = rebuild(a, [], deadline)
    baseline_hash = write_aig(out / "replay_without_build.aig", baseline)
    product_hash = write_aig(out / "product.aig", product)
    gain = len(baseline["gates"]) - len(product["gates"])
    require(not chosen or gain > 0, "nonpositive exact selected-set cleanup")
    write_json(out / "selection.json", dict(selected=chosen, rejected=rejected,
                                            realization=product["realization"]))
    result = dict(status="BUILT", selected_builds=len(chosen),
                  original_and=a.na, replay_without_build_and=len(baseline["gates"]),
                  baseline_cleanup_delta=a.na - len(baseline["gates"]), product_and=len(product["gates"]),
                  exact_same_selected_set_build_gain=gain,
                  conservative_selected_gain_sum=sum(c["conservative_gain"] for c in chosen),
                  replay_without_build_sha256=baseline_hash, product_sha256=product_hash,
                  input_sha256=sha(input_path), proof="ORIGINAL_RESET_AND_UNRESTRICTED_ONE_STEP_UNSAT",
                  all_selected_free_sat_witness_replayed=True,
                  independent_dsec=dict(status="NOT_RUN"),
                  baseline_dsec=dict(status="NOT_RUN"),
                  validated_standalone_noncomb_build_gain=None,
                  production_integration="NOT_RUN", native_recipe_novelty="NOT_CHECKED")
    if deadline is not None:
        deadline.remaining()
    require(sha(input_path) == actual_input_sha256, "input changed before product proof")
    if abc is not None:
        result["baseline_dsec"] = dsec(abc, input_path, out / "replay_without_build.aig", out, dsec_seconds, "baseline_dsec")
        result["independent_dsec"] = dsec(abc, input_path, out / "product.aig", out, dsec_seconds)
        if result["independent_dsec"]["status"] == result["baseline_dsec"]["status"] == "PASS":
            result["validated_standalone_noncomb_build_gain"] = gain
    require(sha(input_path) == actual_input_sha256, "input changed during product proof")
    write_json(out / "product_result.json", result)
    return result
