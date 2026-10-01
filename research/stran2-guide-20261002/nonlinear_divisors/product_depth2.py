#!/usr/bin/env python3
"""Explicit depth-one/depth-two certificate bridge; frozen product.py unchanged."""
import hashlib
import json
import re

from prototype import Aiger, Structure, require, sha, write_json
from product import select, rebuild, write_aig, dsec

def candidate_certificate_sha(candidate):
    original = {key: value for key, value in candidate.items() if key != "depth2_certificate"}
    return hashlib.sha256(json.dumps(original, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def certificate_kind(candidate, input_sha256):
    """Accept only the two explicit complete sufficient proof predicates.

    The optional depth-two certificate is separate from the original proof:
    original step SAT is retained, never rewritten as UNSAT. A bridge must bind
    raw query evidence before attaching the extra certificate.
    """
    p = candidate["proof"]
    require(p["free"] == "SAT" and p["free_witness_replayed"], "missing free SAT/witness proof")
    certificate = candidate.get("depth2_certificate")
    if certificate is None:
        require(candidate["qualified_offline_opportunity"] and p["reset"] == p["step"] == "UNSAT",
                "unproved candidate cannot enter product")
        return "RESET_IMAGE_1"
    require(certificate.get("schema") == 1 and certificate.get("kind") == "RESET_PREFIX_IMAGE" and
            type(certificate.get("depth")) is int and certificate["depth"] == 2,
            "unsupported sequential certificate kind/depth")
    require(certificate.get("input_sha256") == input_sha256 and
            certificate.get("candidate_sha256") == candidate_certificate_sha(candidate),
            "depth-two certificate identity mismatch")
    require(certificate.get("reset_prefix") == ["UNSAT", "UNSAT"] and
            certificate.get("unrestricted_image") == "UNSAT" and
            certificate.get("free_witness_replayed") is True,
            "incomplete depth-two sequential certificate")
    require(certificate.get("fresh_recheck") == "PASS" and
            isinstance(certificate.get("evidence_sha256"), dict) and
            all(isinstance(certificate["evidence_sha256"].get(key), str) and
                re.fullmatch(r"[0-9a-f]{64}", certificate["evidence_sha256"][key])
                for key in ("cnf", "queries", "results", "query_order")),
            "missing bound depth-two recheck evidence")
    return "RESET_PREFIX_IMAGE_2"


def create_certified_product(input_path, candidates, out, abc=None, dsec_seconds=120,
                   expected_input_sha256=None, deadline=None):
    actual_input_sha256 = sha(input_path)
    if expected_input_sha256 is not None:
        require(actual_input_sha256 == expected_input_sha256, "input changed after candidate proof")
    a = Aiger(input_path)
    require(sha(input_path) == actual_input_sha256, "input changed during parsing")
    if deadline is not None:
        deadline.remaining()
    s = Structure(a)
    kinds = {c["root"]: certificate_kind(c, actual_input_sha256) for c in candidates}
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
    result["selected_certificate_kinds"] = {str(c["root"]): certificate_kind(c, actual_input_sha256) for c in chosen}
    if any(kind == "RESET_PREFIX_IMAGE_2" for kind in result["selected_certificate_kinds"].values()):
        result["proof"] = "EXPLICIT_ORIGINAL_RESET_PREFIX_IMAGE_CERTIFICATES"
    if abc is not None:
        result["baseline_dsec"] = dsec(abc, input_path, out / "replay_without_build.aig", out, dsec_seconds, "baseline_dsec")
        result["independent_dsec"] = dsec(abc, input_path, out / "product.aig", out, dsec_seconds)
        if result["independent_dsec"]["status"] == result["baseline_dsec"]["status"] == "PASS":
            result["validated_standalone_noncomb_build_gain"] = gain
    require(sha(input_path) == actual_input_sha256, "input changed during product proof")
    write_json(out / "product_result.json", result)
    return result
