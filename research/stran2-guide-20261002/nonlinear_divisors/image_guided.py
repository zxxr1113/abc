"""Opt-in image-model guidance for the existing hardened anytime controller.

Image samples constrain only the reset + unrestricted-one-step-image search
class. They are not reachable teachers and never discharge proof obligations.
Pool/rank/alias selection stays frozen at initial signatures, while construction
restarts from scratch on each new relevant constraint version.
"""
from __future__ import annotations

from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import sys
import time

import prototype as p

DIAGNOSTIC = Path(__file__).resolve().parents[1] / "image_cegar_diagnostic"
sys.path.insert(0, str(DIAGNOSTIC))
import diagnostic as d
p.require(Path(d.__file__).resolve() == DIAGNOSTIC / "diagnostic.py", "wrong model replay module")

RUNTIME = ["nonlinear_divisors/image_guided.py", "image_cegar_diagnostic/diagnostic.py",
           "image_cegar_diagnostic/model_solver.c", "image_cegar_diagnostic/build_model_solver.sh"]
DOMAIN = "unrestricted_one_step_image"


def signature_hash(seq, mask):
    return hashlib.sha256(json.dumps([seq, mask], separators=(",", ":")).encode()).hexdigest()


def select_new_samples(roots, seq, mask, samples, sample_keys, seen_keys):
    """Only new complete domain assignments adding a root/pool constraint pass.

    The projection includes the target and every frozen pool node. A row already
    present on that projection cannot distinguish any expression over that pool.
    Hash-reused nodes are Boolean functions of the same expressions, so no
    dependency is lost by checking the complete external frozen-pool projection.
    """
    p.require(len(samples) == len(sample_keys), "sample/key cardinality mismatch")
    projections = []
    for root in roots:
        nodes = [root["root"]] + list(root["pool"])
        rows = {tuple((seq[node] >> lane) & 1 for node in nodes) for lane in range(mask.bit_length())}
        projections.append((root["root"], nodes, rows))
    chosen, decisions = [], []
    for index, (sample, key) in enumerate(zip(samples, sample_keys)):
        p.require(len(sample) == len(seq) and all(type(x) is int and x in (0, 1) for x in sample),
                  "incomplete/non-Boolean domain sample")
        key = tuple(key)
        if key in seen_keys:
            decisions.append(dict(sample_index=index, decision="EXACT_DUPLICATE", relevant_roots=[]))
            continue
        new = [(root, nodes, rows, tuple(sample[node] for node in nodes))
               for root, nodes, rows in projections]
        relevant = [root for root, _, rows, row in new if row not in rows]
        if not relevant:
            decisions.append(dict(sample_index=index, decision="PROJECTION_REDUNDANT", relevant_roots=[]))
            continue
        seen_keys.add(key)
        chosen.append(sample)
        for _, _, rows, row in new:
            rows.add(row)
        decisions.append(dict(sample_index=index, decision="APPEND_IMAGE_CONSTRAINT", relevant_roots=relevant))
    return chosen, decisions


class ImageGuidance:
    def __init__(self, a, graph, base, step, seq, mask, free, free_mask,
                 structure, config, job, deadline, helper_identity):
        self.a, self.graph, self.base, self.step = a, graph, base, step
        self.seq, self.mask = list(seq), mask
        self.free, self.free_mask = free, free_mask
        self.structure, self.config = structure, config
        self.job, self.deadline = job, deadline
        self.helper = Path(job["image_model_solver"]) if job.get("image_model_solver") else None
        self.helper_identity = tuple(helper_identity) if helper_identity is not None else None
        self.helper_hash = job.get("image_model_solver_sha256")
        self.version, self.round = 0, 0
        self.attempted, self.model_attempted = set(), set()
        self.seen_keys = {tuple((seq[node] >> lane) & 1 for node in range(1, 1 + a.ni + a.nl))
                          for lane in range(mask.bit_length())}
        self.metrics = Counter()
        self.search_cache = {}
        self.initial_hash = signature_hash(seq, mask)
        self.free_guidance = None
        self.free_only_revisited = set()
        if job.get("predecessor_free"):
            from free_guided import PredecessorFreeDomain
            self.free_guidance = PredecessorFreeDomain(a, graph, base, step, free, free_mask,
                                                       job, config, deadline)

    def annotate(self, candidates):
        for candidate in candidates:
            candidate["image_guidance"] = dict(schema=1, teacher_version=self.version,
                construction_signature_bits=self.mask.bit_length(),
                pool_signature_version=0, pool_signature_sha256=self.initial_hash,
                added_domain=DOMAIN, reachable_teacher=False,
                proof_class="reset_zero_plus_unrestricted_one_step_image",
                proof_source="independent ordinary solver on immutable original transition")
        if self.free_guidance:
            self.free_guidance.annotate(candidates)

    def remember_search(self, root, pool, pool_info, candidates, stats):
        """Remember an exact completed top-k result for this immutable pool."""
        key = (root, tuple(pool))
        p.require(len(set(pool)) == len(pool) and all(0 < node < root for node in pool),
                  "invalid frozen root/pool")
        p.require(all(c["root"] == root for c in candidates), "cached candidate/root mismatch")
        if root in self.search_cache:
            old = self.search_cache[root]
            p.require(old["key"] == key and old["pool_info"] == pool_info, "frozen root/pool mismatch")
        self.search_cache[root] = dict(key=key, pool_info=copy.deepcopy(pool_info),
            candidates=copy.deepcopy(candidates), stats=dict(stats), teacher_version=self.version)
        if self.free_guidance:
            row = dict(root=root, pool=pool)
            self.search_cache[root]["dual_projection"] = self.free_guidance.projection(row, self.seq, self.mask, self.version)

    def checked_cache(self, row):
        p.require(row["root"] in self.search_cache, "unregistered frozen root/pool")
        old = self.search_cache[row["root"]]
        p.require(old["key"] == (row["root"], tuple(row["pool"])) and old["pool_info"] == row["pool_info"],
                  "frozen root/pool mismatch")
        p.require(all(d.candidate_id(c) in self.attempted for c in old["candidates"]),
                  "projection skip would discard an untried cached candidate")
        return old

    def cached_search(self, row):
        old = self.checked_cache(row)
        if self.free_guidance:
            current = self.free_guidance.projection(row, self.seq, self.mask, self.version)
            p.require(current.can_reuse_search(old["dual_projection"]), "free/sequence projection changed before cached search")
        return copy.deepcopy(old["candidates"]), Counter(old["stats"])

    def search_again(self, row, changed):
        if not changed:
            return self.cached_search(row)
        cs, stats = p.search_root(self.structure, row["root"], row["pool"], row["pool_info"],
            self.seq, self.mask, self.free, self.free_mask, self.config, self.deadline)
        self.remember_search(row["root"], row["pool"], row["pool_info"], cs, stats)
        return cs, stats

    def finish_chunk(self, roots):
        if self.free_guidance:
            # Past roots are never revisited by this fixed-prefix controller.
            # Keep dual-domain row sets bounded to the active chunk; proved
            # candidates live in anytime's separate cumulative qualified list.
            for row in roots:
                self.search_cache.pop(row["root"], None)
            self.free_only_revisited.discard(tuple(row["root"] for row in roots))

    def mark_attempted(self, candidates):
        for candidate in candidates:
            identity = d.candidate_id(candidate)
            p.require(identity not in self.attempted, "unchanged candidate proof retry")
            self.attempted.add(identity)

    def collect(self, sources, target):
        """Standalone helper fallback; unchanged query/replay protocol."""
        from anytime import file_identity
        p.require(file_identity(self.helper) == self.helper_identity, "model executable identity changed")
        clone = p.Graph()
        clone.gates, clone.hash = list(self.graph.gates), dict(self.graph.hash)
        samples, model_report = d.collect_models(p, self.a, clone, self.base, self.step, sources,
            target, self.helper, self.deadline, dict(input_sha256=self.job["case"]["input_sha256"],
                teacher_version_before=self.version, added_domain=DOMAIN, reachable_teacher=False,
                pool_signature_sha256=self.initial_hash, helper_expected_sha256=self.helper_hash,
                source_hashes=self.job["source_hashes"]),
            helper_binding=dict(sha256=self.helper_hash, identity=self.helper_identity))
        p.require(file_identity(self.helper) == self.helper_identity, "model executable identity changed")
        provenance = json.loads((target / "provenance.json").read_text())
        p.require(provenance["helper_sha256"] == self.helper_hash, "model executable SHA mismatch")
        return samples, model_report

    def refine(self, roots, candidates, out):
        """Return untried same-pool candidates, or [] when no justified retry exists."""
        self.deadline.remaining()
        p.require(len({r["root"] for r in roots}) == len(roots), "duplicate refinement root")
        for row in roots:
            self.checked_cache(row)  # Bind the change decision to the actual prior search.
        sources = [c for c in candidates if c["proof"]["reset"] == "UNSAT" and
                   c["proof"]["free"] == "SAT" and c["proof"]["step"] == "SAT" and
                   d.candidate_id(c) not in self.model_attempted]
        if not sources:
            self.metrics["no_new_image_sat_source"] += 1
            return []
        self.model_attempted.update(d.candidate_id(c) for c in sources)
        start = time.monotonic()
        target = out / "image_guidance" / f"round_{self.round:05d}"
        target.parent.mkdir(exist_ok=True)
        samples, model_report = self.collect(sources, target)
        replayed = json.loads((target / "replayed_models.json").read_text())
        free_admission = None
        if self.free_guidance:
            # Consume all authenticated rows BEFORE successor/projection dedup.
            free_admission = self.free_guidance.admit(sources, target, model_report, replayed)
            snapshot = self.free_guidance.state.snapshot()
            self.free, self.free_mask = snapshot.signatures, snapshot.mask
            p.write_json(target / "free_admission.json", free_admission)
        indexed = {}
        for row in replayed:
            p.require(row["domain"] == DOMAIN and row["reachable_teacher"] is False and row["replay"] == "PASS",
                      "wrong model domain or unverified replay")
            indexed.setdefault(row["sample_index"], tuple(row["current_inputs"] + row["successor_state"]))
        p.require(set(indexed) == set(range(len(samples))), "incomplete unique sample map")
        added, decisions = select_new_samples(roots, self.seq, self.mask, samples,
                                              [indexed[i] for i in range(len(samples))], self.seen_keys)
        before = self.version
        found, search_stats, executed_stats = [], Counter(), Counter()
        changed_roots = {root for decision in decisions if decision["decision"] == "APPEND_IMAGE_CONSTRAINT"
                         for root in decision["relevant_roots"]}
        discovery_wall_s, skipped_roots, searched_roots = 0.0, 0, 0
        if added:
            self.seq, self.mask = d.append_samples(self.seq, self.mask, added)
            self.version += 1
        free_changed_roots, free_only_capped = set(), False
        if self.free_guidance:
            changed_roots = set()
            for row in roots:
                previous = self.checked_cache(row)["dual_projection"]
                current = self.free_guidance.projection(row, self.seq, self.mask, self.version)
                if current.free_rows != previous.free_rows:
                    free_changed_roots.add(row["root"])
                if not current.can_reuse_search(previous):
                    changed_roots.add(row["root"])
            # Bound only additional free-only revisits. New worlds still apply
            # to later initial roots, and no existing proof is discarded.
            chunk_key = tuple(row["root"] for row in roots)
            if not added and free_changed_roots:
                free_only_capped = chunk_key in self.free_only_revisited
                if not free_only_capped:
                    self.free_only_revisited.add(chunk_key)
        perform_search = bool(added or free_changed_roots) and not free_only_capped
        if perform_search:
            # Pair/frontier/signature iterator state is local to search_root and
            # recreated completely. Frozen root pools never see learned rows.
            with (target / "root_search.jsonl").open("w", buffering=1) as log:
                for row in roots:
                    self.deadline.remaining()
                    start_search = time.monotonic()
                    if row["root"] in changed_roots:
                        cs, stats = self.search_again(row, changed=True)
                        executed_stats.update(stats)
                        searched_roots += 1
                    else:
                        # Complete target/pool rows are unchanged in every
                        # active discovery domain; cached_search checks both
                        # explicitly when predecessor-free is enabled.
                        cs, stats = self.search_again(row, changed=False)
                        skipped_roots += 1
                    discovery_wall_s += time.monotonic() - start_search
                    search_stats.update(stats)  # Logical outcomes include exact cached results.
                    # Keep the baseline top-k policy unchanged. Tried identities
                    # may occupy its cap; [] is not recipe-space exhaustion.
                    fresh = [c for c in cs if d.candidate_id(c) not in self.attempted]
                    found.extend(fresh)
                    log.write(json.dumps(dict(root=row["root"], pool=row["pool"],
                        pool_signature_version=0, teacher_version=self.version,
                        search=dict(stats), candidates=len(cs), untried_candidates=len(fresh),
                        discovery_executed=row["root"] in changed_roots,
                        skip_reason=None if row["root"] in changed_roots else "UNCHANGED_COMPLETE_TARGET_POOL_PROJECTION",
                        **(dict(free_version=self.free_guidance.state.snapshot().version,
                               free_signature_bits=self.free_mask.bit_length(),
                               changed_free_projection=row["root"] in free_changed_roots,
                               cache_domains="sequence_and_free") if self.free_guidance else {})),
                        sort_keys=True) + "\n")
            self.annotate(found)
        self.metrics["model_queries"] += model_report["queries"]
        if self.job.get("inline_image_models"):
            self.metrics["model_cache_misses"] += model_report["model_cache_misses"]
            self.metrics["eligible_step_sat_candidates"] += model_report["eligible_step_sat_candidates"]
            self.metrics["additional_model_solver_queries"] += model_report["additional_solver_queries"]
        self.metrics["model_unknown_skipped"] += model_report["unknown_skipped"]
        self.metrics["independently_replayed_models"] += model_report["models"]
        self.metrics["accepted_image_samples"] += len(added)
        self.metrics["refinement_searches"] += int(perform_search)
        self.metrics["refinement_candidates"] += len(found)
        for key, value in executed_stats.items():
            self.metrics["refinement_" + key] += value
        for key, value in search_stats.items():
            self.metrics["refinement_logical_" + key] += value
        self.metrics["discovery_executed_roots"] += searched_roots
        self.metrics["discovery_skipped_unchanged_projection_roots"] += skipped_roots
        self.metrics["discovery_wall_s"] += discovery_wall_s
        self.metrics["guidance_wall_s"] += time.monotonic() - start
        if self.free_guidance:
            self.metrics["accepted_predecessor_free_worlds"] += free_admission["added"]
            self.metrics["free_only_revisit_cap_stops"] += int(free_only_capped)
            self.metrics["free_only_search_rounds"] += int(perform_search and not added)
        p.write_json(target / "refinement.json", dict(schema=1, teacher_version_before=before,
            teacher_version_after=self.version, added_domain=DOMAIN, reachable_teacher=False,
            construction_signature_bits=self.mask.bit_length(), construction_signature_sha256=signature_hash(self.seq, self.mask),
            pool_signature_version=0, pool_signature_sha256=self.initial_hash,
            exact_key="current_inputs + successor_state", projection="target + entire frozen pool",
            decisions=decisions, accepted_samples=len(added), new_candidates=len(found),
            search=dict(search_stats), search_statistics_scope="logical outcomes including exact cached unchanged-projection results",
            executed_search=dict(executed_stats), discovery_executed_roots=searched_roots,
            discovery_skipped_unchanged_projection_roots=skipped_roots, discovery_wall_s=discovery_wall_s,
            model_report=model_report,
            stopping_reason=(None if found else "FREE_ONLY_REVISIT_CAP" if free_only_capped else
                "NO_UNTRIED_RETURNED_TOPK_CANDIDATE" if perform_search else
                "NO_NEW_RELEVANT_DOMAIN_PROJECTION" if self.free_guidance else "NO_NEW_RELEVANT_IMAGE_CONSTRAINT"),
            **(dict(free_domain=self.free_guidance.report(), free_admission=free_admission,
                    free_changed_roots=sorted(free_changed_roots), free_only_revisit_cap_per_chunk=1,
                    projection_domains="sequence_and_free") if self.free_guidance else {}),
            ordinary_proofs_reused_as_model_proofs=bool(self.job.get("inline_image_models") and model_report["models"]),
            **(dict(model_source="original ordinary step-SAT receipt and projected model",
                    additional_model_solver_queries=0) if self.job.get("inline_image_models") else {})))
        self.round += 1
        self.deadline.remaining()
        return found

    def report(self):
        return dict(**self.metrics, teacher_version=self.version, construction_signature_bits=self.mask.bit_length(),
                    added_domain=DOMAIN, reachable_teacher=False, pool_signature_version=0,
                    pool_signature_sha256=self.initial_hash,
                    candidate_retry_policy="all attempted identities excluded after unchanged per-root top-k, including UNKNOWN",
                    topk_exhaustion_is_recipe_space_exhaustion=False,
                    attribution="Build-only product; selected-root Direct sensitivity audit required separately",
                    **(dict(free_domain=self.free_guidance.report(), free_only_revisit_cap_per_chunk=1,
                            cache_domains="sequence_and_free") if self.free_guidance else {}))
