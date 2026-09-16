#!/usr/bin/env python3
"""Shared parser for &stran's schema-versioned experiment profiles.

The C profiler emits raw seconds, counts, and exact counterfactual gains.  This
module aggregates repeated records (including split-stage runs) and recomputes
all ratios from the raw totals so CSV consumers never add percentages.
"""

from __future__ import annotations

import re
from typing import Any


NA = "N/A"

TIME_PREFIX = "Sequential direct experiment-time profile:"
BUILD_PREFIX = "Sequential direct seq-build experiment profile:"
ROOT_TIME_PREFIX = "stran-root experiment-time profile:"
SIGNATURE_GUIDE_PREFIX = "stran-root signature-guide:"
STRICT_GUIDE_PREFIX = "stran-root strict-signature-guide:"
STRICT_GUIDE_KEYS = ("snapshots", "source-rows", "auxiliary-rows", "skipped-overflow", "prep-sec")
STRICT_CEX_PREFIX = "strict-cex epoch="
STRICT_CEX_KEYS = (
    "epoch", "mode", "solver", "bank", "seen", "added", "duplicate",
    "invalid-reset", "invalid-split", "too-long", "overflow", "ignored-ind",
    "injected", "split-pairs", "seconds", "active-low", "active-queries",
    "active-sat", "active-unsat", "active-unknown", "active-split",
    "active-invalid", "active-size-skip", "active-seconds", "active-conflicts",
    "active-queue-cut",
)
SIGNATURE_GUIDE_KEYS = (
    "roots", "low", "aliases", "changed", "split", "conflicts",
    "rows-before", "rows-after", "sat", "sat-yes", "sat-no", "sat-unknown",
    "prep-sec", "guide-sec", "sat-sec",
)
ROOT_PREPROCESS_DETAIL_PREFIX = "stran-root preprocessing-detail profile:"
ROOT_PAGE_REUSE_DETAIL_PREFIX = "stran-root page-reuse-detail profile:"
ROOT_EFFECT_PREFIX = "stran-root experiment-effect profile:"
ROOT_LANE_PREFIX = "stran-root experiment-proof-lane profile:"
ROOT_SUMMARY_PREFIX = "stran-root experiment-summary profile:"
ROOT_COMMIT_PREFIX = "stran-root experiment-commit profile:"
ROOT_HELPER_PREFIX = "stran-root helper history:"
ROOT_PAGED_PREFIX = "stran-root paged portfolio:"
ROOT_WAVE_PREFIX = "stran-root wave portfolio:"
ROOT_ITERATOR_PREFIX = "stran-root resub iterator:"
ROOT_BUILD_HORIZON_PREFIX = "stran-root build-horizon profile:"
ROOT_KIT_PREFIX = "stran-root Kit portfolio profile:"
ROOT_BDC_PREFIX = "stran-root BDC portfolio profile:"
ROOT_TFO_CORE_PREFIX = "stran-root TFO core-rescue profile:"
ROOT_ISF_TIME_PREFIX = "stran-root ISF time profile:"
ROOT_SEQ_PREFIX = "stran-root sequential relations:"
ROOT_BUILD_FUNNEL_PREFIX = "stran-root build-funnel profile:"
ROOT_BUILD_STAGE_PREFIX = "stran-root build-stage profile:"
ROOT_BUILD_RANK_PREFIX = "stran-root build-rank profile:"
ROOT_BUILD_GATES_PREFIX = "stran-root build-gates profile:"
ROOT_BUILD_GAIN_PREFIX = "stran-root build-gain profile:"
ROOT_BUILD_CI_PREFIX = "stran-root build-ci profile:"
ROOT_BUILD_DIVRANK_PREFIX = "stran-root build-divrank profile:"
ROOT_BUILD_MFFC_PREFIX = "stran-root build-mffc profile:"
ROOT_BUILD_SUPPORT_PREFIX = "stran-root build-support profile:"
ROOT_BUILD_SUPPORT_SIZE_PREFIX = "stran-root build-support-size profile:"
ROOT_BUILD_SUPPORT_MULT_PREFIX = "stran-root build-support-mult profile:"
ROOT_BUILD_SUPPORT_STAGE_PREFIX = "stran-root build-support-stage profile:"
ROOT_BUILD_SUPPORT_ROOT_VALID_PREFIX = (
    "stran-root build-support-root-valid profile:"
)
ROOT_BUILD_SUPPORT_ROOT_ACCEPTED_PREFIX = (
    "stran-root build-support-root-accepted profile:"
)
ROOT_BUILD_RESIDUAL_PREFIX = "stran-root build-residual profile:"
ROOT_BUILD_RESIDUAL_DEPTH_PREFIX = (
    "stran-root build-residual-depth profile:"
)
ROOT_BUILD_RESIDUAL_SIZE_PREFIX = (
    "stran-root build-residual-size profile:"
)
ROOT_BUILD_GREEDY_FRONTIER_PREFIX = (
    "stran-root build-greedy-frontier profile:"
)
ROOT_BUILD_GREEDY_PIVOT_RANK_PREFIX = (
    "stran-root build-greedy-pivot-rank profile:"
)
ROOT_BUILD_GREEDY_PIVOT_NOVELTY_PREFIX = (
    "stran-root build-greedy-pivot-novelty profile:"
)
ROOT_BUILD_GREEDY_PIVOT_COVERAGE_PREFIX = (
    "stran-root build-greedy-pivot-coverage profile:"
)
ROOT_BUILD_GREEDY_PIVOT_KIND_PREFIX = (
    "stran-root build-greedy-pivot-kind profile:"
)
ROOT_BUILD_GREEDY_PIVOT_STATE_PREFIX = (
    "stran-root build-greedy-pivot-state profile:"
)
ROOT_BUILD_GREEDY_MULTIPATH_SUMMARY_PREFIX = (
    "stran-root build-greedy-multipath-summary profile:"
)
ROOT_BUILD_GREEDY_PATH_PREFIX = (
    "stran-root build-greedy-path profile:"
)
STRAN2_CEX_PREFIX = "stran2 CEX corpus:"
STRAN2_INITIAL_SCORR_PREFIX = "stran2 initial scorr profile:"
STRAN2_PLACEMENT_PREFIX = "stran2 CEX placement:"
STRAN2_SIGNATURE_PREFIX = "stran2 CEX trace signature:"
STRAN2_SIGNATURE_LEGACY_PREFIX = "stran2 teaching signature:"
STRAN2_TEACHING_PREFIX = "stran2 root-batch summary:"
STRAN2_TEACHING_LEGACY_PREFIX = "stran2 teaching summary:"

TIME_KEYS = (
    "total-sec", "sim-sec", "care-sec", "root-discovery-sec",
    "direct-discovery-sec", "build-discovery-sec", "gain-eval-sec",
    "proof-build-sec", "comb-proof-sec", "seq-proof-shared-sec",
    "selection-sec", "stage-eval-sec", "contribution-eval-sec",
    "commit-sec", "decision-sec", "profile-overhead-sec", "cex-sec", "shadow-sec",
    "unprofiled-sec",
)

BUILD_KEYS = (
    "generated", "generated-gates", "submitted", "submitted-gates",
    "comb-proved", "seq-proved", "comb-selected", "seq-selected",
    "comb-proved-gates", "seq-proved-gates", "comb-selected-gates",
    "seq-selected-gates", "seq-build-ordered-and-gain",
    "seq-total-and-gain", "seq-direct-only-and-gain",
    "seq-build-only-and-gain", "seq-interaction-and-gain",
    "seq-build-shapley-and-gain", "seq-build-ordered-reg-gain",
    "seq-total-reg-gain", "seq-direct-only-reg-gain",
    "seq-build-only-reg-gain", "seq-interaction-reg-gain",
    "seq-build-shapley-reg-gain", "final-and-gain", "final-reg-gain",
)

ROOT_TIME_KEYS = (
    "total-sec", "sim-sec", "root-refresh-sec", "direct-discovery-sec",
    "divisor-discovery-sec", "resub-init-sec", "resub-enum-sec",
    "isf-portfolio-sec",
    "cbs-graph-sec", "cbs-screen-sec", "cbs-solve-sec",
    "scorr-graph-sec", "scorr-bmc-sec", "scorr-induction-sec",
    "scorr-resim-sec", "scorr-other-sec", "selection-repair-sec",
    "bundle-sec", "cleanup-sec", "exact-audit-sec", "shadow-sec",
    "unprofiled-sec",
)

ROOT_ISF_TIME_KEYS = (
    "portfolio-sec", "rescue-core-sec", "regular-core-sec",
    "projection-sec", "kit-synthesis-sec", "bdc-synthesis-sec",
)
ROOT_ISF_TIME_FIELDS = [
    f"root_isf_{key.replace('-', '_')}" for key in ROOT_ISF_TIME_KEYS
]
ROOT_PHASE_ISF_TIME_FIELDS = [
    f"root_{phase}_isf_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in ROOT_ISF_TIME_KEYS
]

ROOT_PREPROCESS_DETAIL_KEYS = (
    "exp-ci-hit", "exp-ci-miss", "exp-score-sec", "exp-ci-sec",
    "exp-obs-roots", "exp-obs-conflict", "exp-full-roots", "exp-full-conflict",
    "exp-obs-total", "exp-obs-unique", "exp-pruned", "exp-obs-sec",
    "exp-zero-build-sec", "exp-positive-build-sec", "exp-zero-rank-sec",
    "exp-positive-rank-sec",
    "div-collect-sec", "div-rank-sec", "div-select-sec", "div-hash-sec",
    "frontier-dead-sec", "root-potential-sec", "frontier-loop-sec",
    "frontier-support-sec", "frontier-gain-sec", "frontier-sort-sec",
    "frontier-pair-scans", "frontier-matched",
)

ROOT_PREPROCESS_DETAIL_FIELDS = [
    f"root_preprocess_{key.replace('-', '_')}"
    for key in ROOT_PREPROCESS_DETAIL_KEYS
]
ROOT_PHASE_PREPROCESS_DETAIL_FIELDS = [
    f"root_{phase}_preprocess_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in ROOT_PREPROCESS_DETAIL_KEYS
]

ROOT_PAGE_REUSE_DETAIL_KEYS = (
    "rank-mffc-one-first-sec", "rank-mffc-one-cont-sec",
    "rank-eligible-first-sec", "rank-eligible-cont-sec",
    "rank-mffc-one-first-calls", "rank-mffc-one-cont-calls",
    "rank-eligible-first-calls", "rank-eligible-cont-calls",
    "frontier-loop-first-sec", "frontier-loop-cont-sec",
    "frontier-pair-scans-first", "frontier-pair-scans-cont",
    "mffc-one-page-skips",
)
ROOT_PAGE_REUSE_DETAIL_FIELDS = [
    f"root_page_reuse_{key.replace('-', '_')}"
    for key in ROOT_PAGE_REUSE_DETAIL_KEYS
]
ROOT_PHASE_PAGE_REUSE_DETAIL_FIELDS = [
    f"root_{phase}_page_reuse_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in ROOT_PAGE_REUSE_DETAIL_KEYS
]

# Schema 9/10 diagnosis emitted by the production implementation.
DIAG_PREFIX = "stran-root diagnosis profile:"
DIAG_SPEC = {
    "mffc-work": (range(8), ("calls", "next", "accepted", "enum-sec", "build-sec")),
    "mffc-origin": (range(16), ("generated", "proved", "selected", "selected-and-gain")),
    "root": (range(8), ("roots", "started", "exhausted", "next", "raw", "valid",
        "positive", "nonpositive", "duplicate", "collapsed", "invalid",
        "accepted", "pivots", "enum-sec", "build-sec")),
    "gate": (range(64), ("count", "accepted", "nonpositive", "boundary", "rescued", "next-sec")),
    "reject": ([8*s+b for s in (1, 3, 4, 5) for b in range(8)], ("count", "next-sec")),
    "time": ([0], ("iterator-sec", "decode-sec", "exhausted-iterator-sec")),
}
DIAG_FIELDS = [
    f"diag_{phase}_{family.replace('-', '_')}_{bucket}_{key.replace('-', '_')}"
    for phase in ("all", "comb", "seq")
    for family, (buckets, keys) in DIAG_SPEC.items()
    for bucket in buckets
    for key in keys
]

ROOT_PROFILE_FIELDS = [
    f"profile_{key.replace('-', '_')}"
    for key in ROOT_TIME_KEYS
    if key not in {"total-sec", "sim-sec", "direct-discovery-sec",
                   "shadow-sec", "unprofiled-sec"}
]

# Root-mode schema 5 exposes two independent 2 x 3 matrices.  The stage matrix
# is the original algorithm phase (initial COMB or later SEQ) crossed with
# candidate kind; the lane matrix is the proof engine (CBS or scorr).  Older
# schemas used stage for the proof lane, which is why schema 5 is explicit.
ROOT_EFFECT_METRICS = (
    "generated", "submitted", "proved", "selected", "and_gain", "reg_gain",
)
ROOT_EFFECT_FIELDS = [
    f"{stage}_stage_{kind}_{metric}"
    for stage in ("comb", "seq")
    for kind in ("constant", "existing", "build")
    for metric in ROOT_EFFECT_METRICS
]
ROOT_LANE_METRICS = ("submitted", "proved", "selected")
ROOT_LANE_FIELDS = [
    f"{lane}_lane_{kind}_{metric}"
    for lane in ("cbs", "scorr")
    for kind in ("constant", "existing", "build")
    for metric in ROOT_LANE_METRICS
]
ROOT_STAGE_GAIN_FIELDS = [
    f"{stage}_stage_{metric}_gain"
    for stage in ("comb", "seq")
    for metric in ("and", "reg")
]
ROOT_STAGE_SIZE_FIELDS = [
    f"{stage}_stage_{metric}_{point}"
    for stage in ("comb", "seq")
    for metric in ("and", "reg")
    for point in ("before", "after")
]

# History watermarks and materialization/proof events deliberately have
# different names.  In particular, selected may include an old certificate
# and therefore must not be compared only with this snapshot's new-proved.
ROOT_HISTORY_FIELDS = [
    "root_helper_injected_events", "root_helper_inactive_events",
    "root_helper_retained_max", "root_helper_active_events",
    "root_helper_dormant_events", "root_helper_dedup",
    "root_helper_invalidated", "root_helper_classes",
    "root_helper_endpoints_max", "root_helper_materialized_gates",
    "root_batch_relations_max", "root_srm_nodes_max",
    "root_new_proved", "root_history_proved_selected",
    "root_proof_waves", "root_wave_continuations",
    "root_proof_pages", "root_page_continuations",
]
ROOT_SEQ_FIELDS = [
    "root_seq_obligations", "root_seq_seeded", "root_seq_helper_seeds",
    "root_seq_proved", "root_seq_split", "root_seq_unknown",
]
ROOT_ITERATOR_FIELDS = [
    "root_iterator_initialized", "root_iterator_next",
    "root_iterator_q_wave_stops",
    "root_iterator_exhausted", "root_iterator_q_page_stops",
    "root_iterator_snapshot_discarded", "root_iterator_live_max",
    "root_iterator_live_final", "root_iterator_invalid",
]
ROOT_BUILD_HORIZON_FIELDS = [
    "root_build_horizon_records", "root_build_horizon_q_limit_max",
    "root_build_horizon_eligible_roots",
    "root_build_horizon_q_slot_capacity",
    "root_build_horizon_q_slots_used",
    "root_build_horizon_at_q_roots",
    "root_build_horizon_exhausted_before_q_roots",
    "root_build_horizon_unfinished_below_q_roots",
    "root_build_horizon_zero_accepted_roots",
    "root_build_horizon_accepted_total",
    "root_build_horizon_accepted_max_per_root",
    "root_build_horizon_q_slot_utilization_pct",
    "root_build_horizon_at_q_rate_pct",
    "root_build_horizon_exhausted_before_q_rate_pct",
    "root_build_horizon_zero_accepted_rate_pct",
]

ROOT_KIT_KEYS = (
    "core-max", "calls", "separated", "synthesized", "accepted",
    "generated", "submitted", "proved", "selected", "selected-and-gain",
)
ROOT_KIT_FIELDS = [
    f"root_kit_{key.replace('-', '_')}" for key in ROOT_KIT_KEYS
]
ROOT_PHASE_KIT_FIELDS = [
    f"root_{phase}_kit_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in ROOT_KIT_KEYS
]
ROOT_BDC_FIELDS = [
    f"root_bdc_{key.replace('-', '_')}" for key in ROOT_KIT_KEYS
]
ROOT_PHASE_BDC_FIELDS = [
    f"root_{phase}_bdc_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in ROOT_KIT_KEYS
]

ROOT_TFO_CORE_KEYS = (
    "calls", "skipped-no-extra", "exact", "rescued-roots",
    "rescued-nodes", "value-trials", "value-exact", "value-changed",
    "value-unlocked", "value-sec",
)
ROOT_TFO_CORE_FIELDS = [
    f"root_tfo_core_{key.replace('-', '_')}" for key in ROOT_TFO_CORE_KEYS
]
ROOT_PHASE_TFO_CORE_FIELDS = [
    f"root_{phase}_tfo_core_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in ROOT_TFO_CORE_KEYS
]

ROOT_BUILD_FUNNEL_FIELDS = [
    f"root_build_{name}"
    for name in (
        "reservoir_calls", "reservoir_nodes", "reservoir_max",
        "pool_nodes", "pool_max", "pool_empty", "mffc_sum", "mffc_max",
        "mffc_one_skipped", "iterator_next", "semantic_invalid", "collapsed_direct",
        "reject_nonpositive", "reject_known", "reject_direct", "reject_page",
        "accepted",
    )
]
ROOT_PHASE_BUILD_FUNNEL_FIELDS = [
    f"root_{phase}_build_{name}"
    for phase in ("comb", "seq")
    for name in (
        "reservoir_calls", "reservoir_nodes", "reservoir_max",
        "pool_nodes", "pool_max", "pool_empty", "mffc_sum", "mffc_max",
        "mffc_one_skipped", "iterator_next", "semantic_invalid",
        "collapsed_direct", "reject_nonpositive", "reject_known",
        "reject_direct", "reject_page", "accepted",
    )
]
ROOT_BUILD_SUPPORT_KEYS = (
    "valid-candidates", "valid-supports",
    "accepted-candidates", "accepted-supports",
    "submitted-candidates", "submitted-supports",
    "refuted-candidates", "refuted-supports",
    "refuted-bmc-sat-batch-candidates", "refuted-bmc-sat-batch-supports",
    "refuted-ind-only-sat-batch-candidates",
    "refuted-ind-only-sat-batch-supports",
    "refuted-no-sat-batch-candidates", "refuted-no-sat-batch-supports",
    "unknown-candidates", "unknown-supports",
    "proved-candidates", "proved-supports",
    "submitted-no-proof-supports", "submitted-refuted-only-supports",
    "submitted-unknown-only-supports", "submitted-mixed-failure-supports",
    "selected-candidates", "selected-supports",
    "selected-with-accepted-supports", "selected-without-accepted-supports",
    "roots-valid", "roots-accepted",
    "max-valid-candidates-root", "max-valid-supports-root",
    "max-accepted-candidates-root", "max-accepted-supports-root",
    "single-recipe-supports", "multi-recipe-supports",
    "accepted-gate-excess", "proved-min-gate-supports",
    "proved-only-above-min-supports", "selected-min-gate-supports",
    "selected-only-above-min-supports", "selected-below-accepted-min-supports",
)
ROOT_BUILD_SUPPORT_DERIVED = (
    "valid-candidates-per-support", "accepted-candidates-per-support",
    "support-accept-rate-pct", "candidate-submit-rate-pct",
    "support-submit-rate-pct", "submitted-candidate-proof-rate-pct",
    "submitted-candidate-refute-rate-pct",
    "submitted-candidate-unknown-rate-pct",
    "refuted-candidate-bmc-sat-batch-share-pct",
    "refuted-candidate-ind-only-sat-batch-share-pct",
    "refuted-candidate-no-sat-batch-share-pct",
    "submitted-support-proof-rate-pct", "submitted-support-no-proof-rate-pct",
    "support-prove-rate-pct",
    "support-select-rate-pct", "proved-min-gate-share-pct",
    "selected-min-gate-share-pct", "accepted-gate-excess-per-candidate",
)
ROOT_BUILD_SUPPORT_FIELDS = [
    f"root_build_support_{key.replace('-', '_')}"
    for key in (*ROOT_BUILD_SUPPORT_KEYS, *ROOT_BUILD_SUPPORT_DERIVED)
]
ROOT_PHASE_BUILD_SUPPORT_FIELDS = [
    f"root_{phase}_build_support_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in (*ROOT_BUILD_SUPPORT_KEYS, *ROOT_BUILD_SUPPORT_DERIVED)
]
ROOT_BUILD_RESIDUAL_KEYS = (
    "sample-rate", "eligible-roots", "sampled-roots", "no-pair-roots",
    "sampled-pairs", "static-complete-roots", "greedy-complete-roots",
    "static-cover-size-sum", "greedy-cover-size-sum",
    "greedy-valid-supports", "greedy-accepted-supports",
    "greedy-submitted-supports", "greedy-proved-supports",
    "greedy-selected-supports",
)
ROOT_BUILD_RESIDUAL_DERIVED = (
    "sampled-root-rate-pct", "no-pair-root-rate-pct",
    "static-complete-rate-pct", "greedy-complete-rate-pct",
    "static-average-cover-size", "greedy-average-cover-size",
)
ROOT_BUILD_RESIDUAL_FIELDS = [
    f"root_build_residual_{key.replace('-', '_')}"
    for key in (*ROOT_BUILD_RESIDUAL_KEYS, *ROOT_BUILD_RESIDUAL_DERIVED)
]
ROOT_PHASE_BUILD_RESIDUAL_FIELDS = [
    f"root_{phase}_build_residual_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in (*ROOT_BUILD_RESIDUAL_KEYS, *ROOT_BUILD_RESIDUAL_DERIVED)
]
ROOT_BUILD_GREEDY_FRONTIER_KEYS = (
    "roots", "pivots", "unique-states", "duplicate-states", "zero-novel",
    "cover-sum", "novel-sum", "frontier-max", "attempts", "found",
    "time-sec", "schedule-frontiers", "schedule-scored-pivots",
    "schedule-complete", "schedule-time-sec",
    "cache-lookups", "cache-hits", "cache-misses",
    "cache-same-page-hits", "cache-cross-page-hits",
    "cache-fail-hits", "cache-success-hits", "cache-saved-sec",
    "cache-lookup-sec", "cache-payload-bytes", "recursive-calls",
    "recursive-unique", "recursive-duplicates", "recursive-same-page",
    "recursive-cross-page", "recursive-fail-hits",
    "recursive-success-duplicates", "recursive-payload-bytes",
    "recursive-saved-sec", "recursive-lookup-sec", "recursive-dup-depth-0",
    "recursive-dup-depth-1", "recursive-dup-depth-2",
    "recursive-dup-depth-3plus",
)
ROOT_BUILD_GREEDY_FRONTIER_DERIVED = (
    "average-frontier-size", "unique-state-rate-pct",
    "duplicate-state-rate-pct", "zero-novel-rate-pct",
    "novel-cover-share-pct", "attempted-frontier-share-pct",
    "pivot-found-rate-pct", "time-per-attempt-sec",
    "cache-hit-rate-pct", "cache-cross-page-hit-share-pct",
    "cache-fail-hit-share-pct", "cache-saved-over-lookup",
    "recursive-duplicate-rate-pct", "recursive-fail-hit-rate-pct",
    "recursive-cross-page-share-pct", "recursive-saved-over-lookup",
)
ROOT_BUILD_GREEDY_FRONTIER_FIELDS = [
    f"root_build_greedy_frontier_{key.replace('-', '_')}"
    for key in (
        *ROOT_BUILD_GREEDY_FRONTIER_KEYS,
        *ROOT_BUILD_GREEDY_FRONTIER_DERIVED,
    )
]
ROOT_PHASE_BUILD_GREEDY_FRONTIER_FIELDS = [
    f"root_{phase}_build_greedy_frontier_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in (
        *ROOT_BUILD_GREEDY_FRONTIER_KEYS,
        *ROOT_BUILD_GREEDY_FRONTIER_DERIVED,
    )
]
ROOT_BUILD_GREEDY_MULTIPATH_KEYS = (
    "cache-entries", "cache-lookups", "cache-hits", "cache-fail-hits",
    "cache-success-hits", "cache-payload-bytes",
    "duplicate-candidate-fingerprints", "extra-accepted", "extra-q-slots",
)
ROOT_BUILD_GREEDY_MULTIPATH_DERIVED = (
    "cache-hit-rate-pct", "cache-fail-hit-share-pct",
    "duplicate-per-extra-accepted", "extra-q-slot-rate-pct",
)
ROOT_BUILD_GREEDY_MULTIPATH_FIELDS = [
    f"root_build_greedy_multipath_{key.replace('-', '_')}"
    for key in (
        *ROOT_BUILD_GREEDY_MULTIPATH_KEYS,
        *ROOT_BUILD_GREEDY_MULTIPATH_DERIVED,
    )
]
ROOT_PHASE_BUILD_GREEDY_MULTIPATH_FIELDS = [
    f"root_{phase}_build_greedy_multipath_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in (
        *ROOT_BUILD_GREEDY_MULTIPATH_KEYS,
        *ROOT_BUILD_GREEDY_MULTIPATH_DERIVED,
    )
]
ROOT_BUILD_GREEDY_PATH_RANKS = (
    "1", "2", "3", "4", "5", "6", "7", "8", "9+",
)
ROOT_BUILD_GREEDY_PATH_INDICES = (1, 2, 3, 4)
ROOT_BUILD_GREEDY_PATH_METRICS = (
    "attempts", "found", "valid", "valid-gain", "accepted",
    "accepted-gain", "generated", "generated-gain", "proved",
    "proved-gain", "selected", "selected-gain", "selected-and-gain",
    "second-cover-sum", "diversity-new-sum", "diversity-sym-sum",
    "time-sec",
)
ROOT_BUILD_GREEDY_PATH_FIELDS = [
    f"root_build_greedy_path_rank_{rank.replace('-', '_').replace('+', 'plus')}_"
    f"path_{path}_{metric.replace('-', '_').replace('+', 'plus')}"
    for rank in ROOT_BUILD_GREEDY_PATH_RANKS
    for path in ROOT_BUILD_GREEDY_PATH_INDICES
    for metric in ROOT_BUILD_GREEDY_PATH_METRICS
]
ROOT_PHASE_BUILD_GREEDY_PATH_FIELDS = [
    f"root_{phase}_build_greedy_path_rank_"
    f"{rank.replace('-', '_').replace('+', 'plus')}_path_{path}_"
    f"{metric.replace('-', '_').replace('+', 'plus')}"
    for phase in ("comb", "seq")
    for rank in ROOT_BUILD_GREEDY_PATH_RANKS
    for path in ROOT_BUILD_GREEDY_PATH_INDICES
    for metric in ROOT_BUILD_GREEDY_PATH_METRICS
]
ROOT_BUILD_BUCKETS = {
    "stage": (("one-gate", "div-gate", "gate-gate", "greedy"),
              ("valid", "accepted", "generated", "proved", "selected",
               "selected-and-gain", "time-sec")),
    "rank": (("1", "2", "3-4", "5-8", "9-16", "17-32", "33-64", "65+"),
             ("generated", "proved", "selected", "selected-and-gain")),
    "gates": (("1", "2", "3", "4", "5-8", "9+"),
              ("generated", "proved", "selected", "selected-and-gain")),
    "gain": (("1", "2", "3-4", "5-8", "9-16", "17+"),
             ("generated", "proved", "selected", "selected-and-gain")),
    "ci": (("zero", "positive"),
           ("generated", "proved", "selected", "selected-and-gain")),
    "divrank": (("1-4", "5-8", "9-16", "17-32", "33-64", "65+"),
                ("generated", "proved", "selected", "selected-and-gain")),
    "mffc": (("1", "2", "3-4", "5-8", "9-16", "17+"),
             ("calls", "next", "accepted", "time-sec")),
    "support_size": (("1", "2", "3", "4", "5-8", "9+"),
                     ("valid-supports", "accepted-supports",
                      "accepted-candidates", "submitted-supports",
                      "refuted-supports", "unknown-supports",
                      "proved-supports",
                      "selected-supports")),
    "support_mult": (("1", "2", "3-4", "5-8", "9-16", "17+"),
                     ("supports", "candidates", "submitted-supports",
                      "refuted-supports", "unknown-supports",
                      "proved-supports",
                      "selected-supports", "proved-min-gate-supports",
                      "selected-min-gate-supports", "gate-excess")),
    "support_stage": (("one-gate", "div-gate", "gate-gate", "greedy"),
                      ("valid-supports", "accepted-supports",
                       "submitted-supports", "refuted-supports",
                       "unknown-supports", "proved-supports",
                       "selected-supports")),
    "support_root_valid": (("1", "gt1-2", "gt2-4", "gt4-8", "gt8"),
                           ("roots", "candidates", "supports")),
    "support_root_accepted": (("1", "gt1-2", "gt2-4", "gt4-8", "gt8"),
                              ("roots", "candidates", "supports")),
    "residual_depth": (("1", "2", "4", "8", "16", "32"),
                       ("static-covered-pairs", "greedy-covered-pairs",
                        "total-pairs")),
    "residual_size": (("1", "2", "3-4", "5-8", "9-16", "17-32", "33+"),
                      ("static-complete-roots", "greedy-complete-roots")),
    "greedy_pivot_rank": (
        ("1", "2", "3-4", "5-8", "9-16", "17-32", "33-64", "65+"),
        ("attempts", "found", "valid", "accepted", "generated", "proved",
         "selected", "selected-and-gain", "time-sec"),
    ),
    "greedy_pivot_novelty": (
        ("zero", "1-25", "26-50", "51-75", "76-100"),
        ("attempts", "found", "valid", "accepted", "generated", "proved",
         "selected", "selected-and-gain", "time-sec"),
    ),
    "greedy_pivot_coverage": (
        ("zero", "1-25", "26-50", "51-75", "76-100"),
        ("attempts", "found", "valid", "accepted", "generated", "proved",
         "selected", "selected-and-gain", "time-sec"),
    ),
    "greedy_pivot_kind": (
        ("literal", "pair"),
        ("attempts", "found", "valid", "accepted", "generated", "proved",
         "selected", "selected-and-gain", "time-sec"),
    ),
    "greedy_pivot_state": (
        ("unique", "duplicate"),
        ("attempts", "found", "valid", "accepted", "generated", "proved",
         "selected", "selected-and-gain", "time-sec"),
    ),
}


def _field_token(value: str) -> str:
    return value.replace("-", "_").replace("+", "plus")


ROOT_BUILD_BUCKET_FIELDS = [
    f"root_build_{family}_{_field_token(bucket)}_{_field_token(metric)}"
    for family, (buckets, metrics) in ROOT_BUILD_BUCKETS.items()
    for bucket in buckets
    for metric in metrics
]
ROOT_PHASE_BUILD_BUCKET_FIELDS = [
    f"root_{phase}_build_{family}_{_field_token(bucket)}_{_field_token(metric)}"
    for phase in ("comb", "seq")
    for family, (buckets, metrics) in ROOT_BUILD_BUCKETS.items()
    for bucket in buckets
    for metric in metrics
]
PHASE_PROFILE_FIELDS = [
    f"{phase}_profile_{key.replace('-', '_')}"
    for phase in ("comb", "seq")
    for key in dict.fromkeys((*TIME_KEYS, *ROOT_TIME_KEYS))
]

STRAN2_PROFILE_FIELDS = [
    "stran2_initial_scorr_records",
    *[f"stran2_initial_scorr_{key.replace('-', '_')}" for key in (
        "frames", "conflict-limit", "source-and", "result-and",
        "source-reg", "result-reg", "completed", "rounds",
        "bmc-unsat", "bmc-sat", "bmc-unknown", "induction-unsat",
        "induction-sat", "induction-unknown", "conflicts", "total-sec",
        "bmc-sec", "induction-sec", "reduce-sec",
    )],
    "stran2_cex_records", "stran2_cex_retained", "stran2_cex_capacity",
    "stran2_cex_packed_lanes_seen", "stran2_cex_duplicates",
    "stran2_cex_ignored_induction", "stran2_cex_too_long",
    "stran2_cex_words", "stran2_placement_records",
    "stran2_placement_direct_records",
    "stran2_placement_root_batch_records", "stran2_trace_budget_max",
    "stran2_random_fill_max", "stran2_overflow_max",
    "stran2_signature_records",
    "stran2_signature_source_words_max",
    "stran2_signature_random_words_max",
    "stran2_signature_build_words_max",
    "stran2_signature_frames_max", "stran2_signature_source_slots_max",
    "stran2_signature_build_slots_max",
    "stran2_signature_reachable_cex_max",
    "stran2_signature_cex_capacity_max", "stran2_teaching_records",
    "stran2_teaching_root_signatures", "stran2_teaching_selector_calls",
    "stran2_teaching_roots_with_cex", "stran2_teaching_selected_cex",
    "stran2_teaching_distinguishable_proxies",
    "stran2_teaching_covered_proxies",
    "stran2_teaching_selection_and_gather_sec",
    "stran2_teaching_selection_pct_of_profile",
]

PROFILE_FIELDS = [
    "stran_output_proof_enabled", "stran_prefix_proof_boundary", "stran_tail_proof_boundary",
    "stran_tail_feedback", "stran_tail_extra_window", "stran_tail_extra_state",
    "stran_direct_prefix_proof_boundary",
    "tracebuild_mode", "tracebuild_commits", "tracebuild_gain", "tracebuild_proposals",
    "tracebuild_branches", "tracebuild_exhausted", "tracebuild_capped", "tracebuild_proofs",
    "tracebuild_sat", "tracebuild_unknown", "tracebuild_replay", "tracebuild_direct_capable",
    "tracebuild_clauses", "tracebuild_patterns", "tracebuild_material",
    "tracebuild_cost_evaluated", "tracebuild_cost_rejected",
    "tracebuild_old_bound_excluded", "tracebuild_old_bound_positive",
    "tracebuild_old_bound_proved", "tracebuild_zero_new_proved",
    "tracebuild_zero_new_commits", "tracebuild_cost_raw_gates",
    "tracebuild_cost_new_gates",
    "tracebuild_cut_multi", "tracebuild_cut_views", "tracebuild_cut_capped", "tracebuild_cut_kit",
    "tracebuild_cut_bdc", "tracebuild_cut_positive", "tracebuild_cut_proofs",
    "tracebuild_cut_commit_kit", "tracebuild_cut_commit_bdc",
    "tracebuild_cut_old_bound_excluded", "tracebuild_cut_old_bound_positive",
    "tracebuild_cut_old_bound_proved",
    "tracebuild_cut_raw_gates", "tracebuild_cut_new_gates",
    "tracebuild_raw_frames", "tracebuild_kept_frames", "tracebuild_raw_terms", "tracebuild_kept_terms",
    "tracebuild_state_divergent", "tracebuild_state_divergent_gain",
    "tracebuild_root_refuted", "tracebuild_window_refuted",
    "relobs_mode", "relobs_commits", "relobs_gain", "relobs_generated",
    "relobs_constant_generated", "relobs_existing_generated", "relobs_build_generated",
    "relobs_material", "relobs_tried", "relobs_sat", "relobs_unknown", "relobs_replay",
    "relobs_state_divergent", "relobs_root_refuted", "relobs_window_refuted",
    "relobs_state_divergent_gain", "relobs_build_commits", "relobs_build_gain",
    "relobs_direct_commits", "relobs_direct_gain", "relobs_proof_seconds",
    *DIAG_FIELDS,
    "strict_guide_records",
    *[f"strict_guide_{key.replace('-', '_')}" for key in STRICT_GUIDE_KEYS],
    "strict_cex_records",
    *[f"strict_cex_{key.replace('-', '_')}" for key in STRICT_CEX_KEYS],
    "signature_guide_records", "signature_guide_mode", "signature_guide_slots_max",
    *[f"signature_guide_{key.replace('-', '_')}" for key in SIGNATURE_GUIDE_KEYS],
    "profile_schema", "profile_time_records", "profile_seq_build_records",
    "profile_closure_records", "profile_closure_sec", "profile_closure_and_gain",
    "profile_closure_selected", "profile_accounting_complete",
    *[f"{phase}_commit_{kind}_{metric}"
      for phase in ("comb", "seq")
      for kind in ("constant", "existing", "build")
      for metric in ("selected", "and_gain", "reg_gain")],
    *[f"{phase}_commit_cleanup_extra_and_gain" for phase in ("comb", "seq")],
    *[("profile_overhead_sec" if key == "profile-overhead-sec"
       else f"profile_{key.replace('-', '_')}") for key in TIME_KEYS],
    *[key.replace("-", "_")
      if key.startswith(("seq-build-", "seq-total-", "seq-direct-",
                         "seq-interaction-", "final-"))
      else f"seq_build_{key.replace('-', '_')}"
      for key in BUILD_KEYS],
    "profile_build_discovery_pct", "profile_seq_proof_shared_pct",
    "profile_selection_pct", "profile_stage_eval_pct",
    "profile_contribution_eval_pct", "profile_commit_pct",
    "profile_decision_pct", "profile_overhead_pct", "profile_unprofiled_pct",
    "seq_build_total_proved", "seq_build_total_selected",
    "seq_build_proof_rate_pct", "seq_build_seq_fraction_pct",
    "seq_build_seq_selected_rate_pct",
    "seq_build_ordered_seq_gain_share_pct",
    "seq_build_only_seq_gain_share_pct",
    "seq_build_ordered_final_gain_share_pct",
    "seq_build_path_upper_bound_sec", "seq_build_path_upper_bound_pct",
    "seq_build_ordered_gain_per_upper_bound_sec",
    *ROOT_STAGE_GAIN_FIELDS,
    *ROOT_STAGE_SIZE_FIELDS,
    *ROOT_EFFECT_FIELDS,
    *ROOT_LANE_FIELDS,
    *ROOT_HISTORY_FIELDS,
    *ROOT_SEQ_FIELDS,
    *ROOT_ITERATOR_FIELDS,
    *ROOT_BUILD_HORIZON_FIELDS,
    *ROOT_KIT_FIELDS,
    *ROOT_PHASE_KIT_FIELDS,
    *ROOT_BDC_FIELDS,
    *ROOT_PHASE_BDC_FIELDS,
    *ROOT_TFO_CORE_FIELDS,
    *ROOT_PHASE_TFO_CORE_FIELDS,
    *ROOT_ISF_TIME_FIELDS,
    *ROOT_PHASE_ISF_TIME_FIELDS,
    *ROOT_BUILD_FUNNEL_FIELDS,
    *ROOT_PHASE_BUILD_FUNNEL_FIELDS,
    *ROOT_BUILD_SUPPORT_FIELDS,
    *ROOT_PHASE_BUILD_SUPPORT_FIELDS,
    *ROOT_BUILD_RESIDUAL_FIELDS,
    *ROOT_PHASE_BUILD_RESIDUAL_FIELDS,
    *ROOT_BUILD_GREEDY_FRONTIER_FIELDS,
    *ROOT_PHASE_BUILD_GREEDY_FRONTIER_FIELDS,
    *ROOT_BUILD_GREEDY_MULTIPATH_FIELDS,
    *ROOT_PHASE_BUILD_GREEDY_MULTIPATH_FIELDS,
    *ROOT_BUILD_GREEDY_PATH_FIELDS,
    *ROOT_PHASE_BUILD_GREEDY_PATH_FIELDS,
    *ROOT_BUILD_BUCKET_FIELDS,
    *ROOT_PHASE_BUILD_BUCKET_FIELDS,
    *ROOT_PREPROCESS_DETAIL_FIELDS,
    *ROOT_PHASE_PREPROCESS_DETAIL_FIELDS,
    *ROOT_PAGE_REUSE_DETAIL_FIELDS,
    *ROOT_PHASE_PAGE_REUSE_DETAIL_FIELDS,
    *PHASE_PROFILE_FIELDS,
    *ROOT_PROFILE_FIELDS,
    *STRAN2_PROFILE_FIELDS,
]

_KEY_VALUE = re.compile(r"([a-z][a-z0-9-]*)=(-?\d+(?:\.\d+)?)")


def _number(text: str) -> int | float:
    return float(text) if "." in text else int(text)


def _ratio(numerator: Any, denominator: Any) -> Any:
    if not isinstance(numerator, (int, float)):
        return NA
    if not isinstance(denominator, (int, float)) or denominator == 0:
        return NA
    return round(100.0 * numerator / denominator, 6)


def _quotient(numerator: Any, denominator: Any) -> Any:
    if not isinstance(numerator, (int, float)):
        return NA
    if not isinstance(denominator, (int, float)) or denominator == 0:
        return NA
    return round(numerator / denominator, 6)


def _sum_records(records: list[dict[str, int | float]], keys: tuple[str, ...]) -> dict[str, Any]:
    totals: dict[str, Any] = {}
    for key in keys:
        values = [record[key] for record in records if key in record]
        totals[key] = sum(values) if values else NA
    return totals


def _sum_values(record: dict[str, int | float], *keys: str) -> int | float:
    return sum(record.get(key, 0) for key in keys)


def _root_time_to_legacy(record: dict[str, int | float]) -> dict[str, int | float]:
    """Map schema-3 root-only buckets onto the long-lived CSV rollups."""
    build = _sum_values(record, "divisor-discovery-sec", "resub-init-sec",
                        "resub-enum-sec", "isf-portfolio-sec")
    commit = _sum_values(record, "bundle-sec", "cleanup-sec", "exact-audit-sec")
    selection = record.get("selection-repair-sec", 0)
    return {
        "total-sec": record.get("total-sec", 0),
        "sim-sec": record.get("sim-sec", 0),
        "care-sec": 0,
        "root-discovery-sec": record.get("root-refresh-sec", 0),
        "direct-discovery-sec": record.get("direct-discovery-sec", 0),
        "build-discovery-sec": build,
        "gain-eval-sec": 0,
        "proof-build-sec": _sum_values(record, "cbs-graph-sec", "scorr-graph-sec"),
        "comb-proof-sec": _sum_values(record, "cbs-screen-sec", "cbs-solve-sec"),
        "seq-proof-shared-sec": _sum_values(
            record, "scorr-bmc-sec", "scorr-induction-sec",
            "scorr-resim-sec", "scorr-other-sec"),
        "selection-sec": selection,
        "stage-eval-sec": 0,
        "contribution-eval-sec": 0,
        "commit-sec": commit,
        "decision-sec": selection + commit,
        "profile-overhead-sec": 0,
        "cex-sec": 0,
        "shadow-sec": record.get("shadow-sec", 0),
        "unprofiled-sec": record.get("unprofiled-sec", 0),
    }


def _root_effect_to_build(
    effects: list[tuple[str, str, dict[str, int | float]]],
    lanes: list[tuple[str, str, dict[str, int | float]]],
    summaries: list[dict[str, int | float]],
) -> dict[str, int | float]:
    """Aggregate phase and proof-lane matrices into legacy Build rollups."""
    result: dict[str, int | float] = {}
    gains: dict[tuple[str, str, str], int | float] = {}
    for stage, kind, record in effects:
        if kind == "build":
            result["generated"] = result.get("generated", 0) + record.get("generated", 0)
            result["submitted"] = result.get("submitted", 0) + record.get("submitted", 0)
        gains[(stage, kind, "and")] = gains.get((stage, kind, "and"), 0) + record.get("marginal-and", 0)
        gains[(stage, kind, "reg")] = gains.get((stage, kind, "reg"), 0) + record.get("marginal-reg", 0)
    for lane, kind, record in lanes:
        if kind != "build":
            continue
        legacy = "comb" if lane == "cbs" else "seq"
        result[f"{legacy}-proved"] = (
            result.get(f"{legacy}-proved", 0) + record.get("proved", 0)
        )
        result[f"{legacy}-selected"] = (
            result.get(f"{legacy}-selected", 0) + record.get("selected", 0)
        )
    # Schema <=4 used comb/seq stage names for the proof engine itself.
    if not lanes:
        for stage, kind, record in effects:
            if kind != "build":
                continue
            result[f"{stage}-proved"] = (
                result.get(f"{stage}-proved", 0) + record.get("proved", 0)
            )
            result[f"{stage}-selected"] = (
                result.get(f"{stage}-selected", 0) + record.get("selected", 0)
            )
    for metric in ("and", "reg"):
        build = gains.get(("seq", "build", metric), 0)
        direct = gains.get(("seq", "constant", metric), 0) + gains.get(("seq", "existing", metric), 0)
        result[f"seq-build-ordered-{metric}-gain"] = build
        result[f"seq-total-{metric}-gain"] = direct + build
        result[f"seq-direct-only-{metric}-gain"] = direct
        result[f"seq-build-only-{metric}-gain"] = build
        result[f"seq-interaction-{metric}-gain"] = 0
        result[f"seq-build-shapley-{metric}-gain"] = build
    for summary in summaries:
        for key in ("final-and-gain", "final-reg-gain"):
            if key in summary:
                result[key] = result.get(key, 0) + summary[key]
    return result


def _root_effect_matrix(
    effects: list[tuple[str, str, dict[str, int | float]]],
) -> dict[str, int | float]:
    """Aggregate schema-3 comb/seq x constant/existing/Build records."""
    result: dict[str, int | float] = {}
    source_keys = {
        "generated": "generated",
        "submitted": "submitted",
        "proved": "proved",
        "selected": "selected",
        "and_gain": "marginal-and",
        "reg_gain": "marginal-reg",
    }
    for stage, kind, record in effects:
        for metric, source_key in source_keys.items():
            if source_key not in record:
                continue
            field = f"{stage}_stage_{kind}_{metric}"
            result[field] = result.get(field, 0) + record[source_key]

    for stage in ("comb", "seq"):
        for metric in ("and", "reg"):
            fields = [
                f"{stage}_stage_{kind}_{metric}_gain"
                for kind in ("constant", "existing", "build")
            ]
            values = [result[field] for field in fields if field in result]
            if values:
                result[f"{stage}_stage_{metric}_gain"] = sum(values)
    return result


def _root_lane_matrix(
    lanes: list[tuple[str, str, dict[str, int | float]]],
) -> dict[str, int | float]:
    """Aggregate schema-5 CBS/scorr x constant/existing/Build records."""
    result: dict[str, int | float] = {}
    for lane, kind, record in lanes:
        for metric in ROOT_LANE_METRICS:
            if metric not in record:
                continue
            field = f"{lane}_lane_{kind}_{metric}"
            result[field] = result.get(field, 0) + record[metric]
    return result


def _root_summary_stage_gains(
    summaries: list[dict[str, int | float]],
) -> dict[str, int | float]:
    """Use exact cleanup gains, not per-candidate marginal gains, per phase."""
    result: dict[str, int | float] = {}
    for record in summaries:
        phase_id = record.get("phase-id")
        if phase_id not in (0, 1):
            continue
        stage = "comb" if phase_id == 0 else "seq"
        for metric in ("and", "reg"):
            before_key = f"{metric}-before"
            after_key = f"{metric}-after"
            before_field = f"{stage}_stage_{metric}_before"
            after_field = f"{stage}_stage_{metric}_after"
            if before_key in record and before_field not in result:
                result[before_field] = record[before_key]
            if after_key in record:
                result[after_field] = record[after_key]
            key = f"final-{metric}-gain"
            if key in record:
                field = f"{stage}_stage_{metric}_gain"
                result[field] = result.get(field, 0) + record[key]
    return result


def parse_experiment_profile(stdout: str) -> dict[str, Any]:
    """Return fixed-schema metrics from one &stran stdout string."""
    result = {field: NA for field in PROFILE_FIELDS}
    result["stran_output_proof_enabled"] = 0
    for line in stdout.splitlines():
        if line.startswith("stran-proof-boundary "):
            scope = dict(re.findall(r"([\w-]+)=([^\s]+)", line))
            result["stran_output_proof_enabled"] = int(scope["tail"] == "output")
            result["stran_prefix_proof_boundary"] = scope["prefix"]
            result["stran_tail_proof_boundary"] = scope["tail"]
            for key in ("feedback", "extra-window", "extra-state"):
                result["stran_tail_" + key.replace("-", "_")] = int(scope[key])
        elif line.startswith("stran-direct-prefix "):
            scope = dict(re.findall(r"([\w-]+)=([^\s]+)", line))
            result["stran_direct_prefix_proof_boundary"] = scope["boundary"]
    tracebuild = {field: 0 for field in PROFILE_FIELDS if field.startswith("tracebuild_")}
    for line in stdout.splitlines():
        if not line.startswith("tracebuild-"):
            continue
        kv = dict(re.findall(r"([\w-]+)=(-?\d+(?:\.\d+)?)", line))
        if line.startswith("tracebuild-summary "):
            for key in ("mode", "commits", "gain"):
                tracebuild[f"tracebuild_{key}"] = int(kv[key])
        elif line.startswith("tracebuild-search "):
            for key in ("proposals", "branches", "exhausted", "capped", "proofs", "sat", "unknown", "replay", "direct-capable", "clauses", "patterns", "material"):
                tracebuild["tracebuild_" + key.replace("-", "_")] += int(kv[key])
        elif line.startswith("tracebuild-cone "):
            for key in ("raw-frames", "kept-frames", "raw-terms", "kept-terms"):
                tracebuild["tracebuild_" + key.replace("-", "_")] += int(kv[key])
        elif line.startswith("tracebuild-cost "):
            for key in ("evaluated", "rejected"):
                tracebuild["tracebuild_cost_" + key] += int(kv[key])
            for key in ("old-bound-excluded", "old-bound-positive",
                        "old-bound-proved", "zero-new-proved",
                        "zero-new-commits"):
                tracebuild["tracebuild_" + key.replace("-", "_")] += int(kv[key])
            tracebuild["tracebuild_cost_raw_gates"] += int(kv["raw-gates"])
            tracebuild["tracebuild_cost_new_gates"] += int(kv["new-gates"])
        elif line.startswith("tracebuild-cut "):
            for key in ("multi", "views", "capped", "kit", "bdc", "positive",
                        "proofs", "commit-kit", "commit-bdc", "old-bound-excluded",
                        "old-bound-positive", "old-bound-proved"):
                tracebuild["tracebuild_cut_" + key.replace("-", "_")] += int(kv[key])
            tracebuild["tracebuild_cut_raw_gates"] += int(kv["raw-gates"])
            tracebuild["tracebuild_cut_new_gates"] += int(kv["new-gates"])
        elif line.startswith("tracebuild-commit "):
            for key, field in (("root-status", "root_refuted"), ("window-status", "window_refuted"), ("state-status", "state_divergent")):
                tracebuild["tracebuild_" + field] += int(kv[key]) == 0
            if int(kv["state-status"]) == 0:
                tracebuild["tracebuild_state_divergent_gain"] += int(kv["gain"])
    result.update(tracebuild)
    relobs = {field: 0 for field in PROFILE_FIELDS if field.startswith("relobs_")}
    for line in stdout.splitlines():
        if not line.startswith("relobs-"):
            continue
        kv = dict(re.findall(r"([\w-]+)=(-?\d+(?:\.\d+)?)", line))
        if line.startswith("relobs-summary "):
            for key in ("mode", "commits", "gain"):
                relobs[f"relobs_{key}"] = int(kv[key])
        elif line.startswith("relobs-discovery "):
            for key, field in (("candidates", "generated"), ("material", "material"),
                               ("constant", "constant_generated"), ("existing", "existing_generated"),
                               ("build", "build_generated")):
                relobs[f"relobs_{field}"] += int(kv[key])
        elif line.startswith("relobs-round "):
            for key in ("tried", "sat", "unknown", "replay"):
                relobs[f"relobs_{key}"] += int(kv[key])
        elif line.startswith("relobs-commit "):
            gain = int(kv["gain"])
            kind = "build" if int(kv["kind"]) == 2 else "direct"
            relobs[f"relobs_{kind}_commits"] += 1
            relobs[f"relobs_{kind}_gain"] += gain
            for key, field in (("root-status", "root_refuted"), ("window-status", "window_refuted"),
                               ("state-status", "state_divergent")):
                relobs[f"relobs_{field}"] += int(kv[key]) == 0
            if int(kv["state-status"]) == 0:
                relobs["relobs_state_divergent_gain"] += gain
        elif line.startswith("relobs-proof "):
            relobs["relobs_proof_seconds"] += float(kv["seconds"])
    result.update(relobs)
    time_records: list[dict[str, int | float]] = []
    build_records: list[dict[str, int | float]] = []
    root_time_records: list[dict[str, int | float]] = []
    root_phase_time_records: dict[str, list[dict[str, int | float]]] = {
        "comb": [], "seq": [],
    }
    root_preprocess_detail_records: list[dict[str, int | float]] = []
    root_phase_preprocess_detail_records: dict[
        str, list[dict[str, int | float]]
    ] = {"comb": [], "seq": []}
    root_page_reuse_detail_records: list[dict[str, int | float]] = []
    root_phase_page_reuse_detail_records: dict[
        str, list[dict[str, int | float]]
    ] = {"comb": [], "seq": []}
    root_effects: list[tuple[str, str, dict[str, int | float]]] = []
    root_lanes: list[tuple[str, str, dict[str, int | float]]] = []
    root_summaries: list[dict[str, int | float]] = []
    root_commits: list[tuple[str, str, dict[str, int | float]]] = []
    closure_times: list[dict[str, int | float]] = []
    closure_summaries: list[dict[str, int | float]] = []
    root_helpers: list[dict[str, int | float]] = []
    root_paged: list[dict[str, int | float]] = []
    root_iterators: list[dict[str, int | float]] = []
    root_build_horizons: list[dict[str, int | float]] = []
    root_kit_records: list[dict[str, int | float]] = []
    root_phase_kit_records: dict[str, list[dict[str, int | float]]] = {
        "comb": [], "seq": [],
    }
    root_bdc_records: list[dict[str, int | float]] = []
    root_phase_bdc_records: dict[str, list[dict[str, int | float]]] = {
        "comb": [], "seq": [],
    }
    root_tfo_core_records: list[dict[str, int | float]] = []
    root_phase_tfo_core_records: dict[
        str, list[dict[str, int | float]]
    ] = {"comb": [], "seq": []}
    root_isf_time_records: list[dict[str, int | float]] = []
    root_phase_isf_time_records: dict[str, list[dict[str, int | float]]] = {
        "comb": [], "seq": [],
    }
    root_seq: list[dict[str, int | float]] = []
    root_build_funnels: list[dict[str, int | float]] = []
    root_phase_build_funnels: dict[str, list[dict[str, int | float]]] = {
        "comb": [], "seq": [],
    }
    root_build_supports: list[dict[str, int | float]] = []
    root_phase_build_supports: dict[str, list[dict[str, int | float]]] = {
        "comb": [], "seq": [],
    }
    root_build_residuals: list[dict[str, int | float]] = []
    root_phase_build_residuals: dict[str, list[dict[str, int | float]]] = {
        "comb": [], "seq": [],
    }
    root_build_greedy_frontiers: list[dict[str, int | float]] = []
    root_phase_build_greedy_frontiers: dict[
        str, list[dict[str, int | float]]
    ] = {"comb": [], "seq": []}
    root_build_greedy_multipath: list[dict[str, int | float]] = []
    root_phase_build_greedy_multipath: dict[
        str, list[dict[str, int | float]]
    ] = {"comb": [], "seq": []}
    root_build_greedy_paths: list[
        tuple[str, int, dict[str, int | float]]
    ] = []
    root_phase_build_greedy_paths: dict[
        str, list[tuple[str, int, dict[str, int | float]]]
    ] = {"comb": [], "seq": []}
    root_build_buckets: dict[str, list[tuple[str, dict[str, int | float]]]] = {
        family: [] for family in ROOT_BUILD_BUCKETS
    }
    root_phase_build_buckets = {
        phase: {family: [] for family in ROOT_BUILD_BUCKETS}
        for phase in ("comb", "seq")
    }
    stran2_cex_records: list[dict[str, int | float]] = []
    stran2_initial_scorr_records: list[dict[str, int | float]] = []
    stran2_placement_records: list[dict[str, int | float]] = []
    stran2_signature_records: list[dict[str, int | float]] = []
    stran2_teaching_records: list[dict[str, int | float]] = []
    signature_guide_records: list[dict[str, int | float]] = []
    strict_guide_records: list[dict[str, int | float]] = []
    strict_cex_records: list[dict[str, int | float]] = []
    diagnosis: dict[str, int | float] = {}
    schemas: list[int] = []
    for line in stdout.splitlines():
        if not any(prefix in line for prefix in (
            DIAG_PREFIX, TIME_PREFIX, BUILD_PREFIX, ROOT_TIME_PREFIX, SIGNATURE_GUIDE_PREFIX, STRICT_CEX_PREFIX, STRICT_GUIDE_PREFIX,
            ROOT_PREPROCESS_DETAIL_PREFIX,
            ROOT_PAGE_REUSE_DETAIL_PREFIX,
            ROOT_EFFECT_PREFIX, ROOT_LANE_PREFIX, ROOT_SUMMARY_PREFIX, ROOT_COMMIT_PREFIX,
            ROOT_HELPER_PREFIX,
            ROOT_PAGED_PREFIX, ROOT_WAVE_PREFIX,
            ROOT_ITERATOR_PREFIX, ROOT_BUILD_HORIZON_PREFIX, ROOT_KIT_PREFIX,
            ROOT_BDC_PREFIX, ROOT_TFO_CORE_PREFIX, ROOT_ISF_TIME_PREFIX,
            ROOT_SEQ_PREFIX,
            ROOT_BUILD_FUNNEL_PREFIX, ROOT_BUILD_STAGE_PREFIX,
            ROOT_BUILD_RANK_PREFIX, ROOT_BUILD_GATES_PREFIX,
            ROOT_BUILD_GAIN_PREFIX, ROOT_BUILD_CI_PREFIX,
            ROOT_BUILD_DIVRANK_PREFIX,
            ROOT_BUILD_MFFC_PREFIX,
            ROOT_BUILD_SUPPORT_PREFIX, ROOT_BUILD_SUPPORT_SIZE_PREFIX,
            ROOT_BUILD_SUPPORT_MULT_PREFIX, ROOT_BUILD_SUPPORT_STAGE_PREFIX,
            ROOT_BUILD_SUPPORT_ROOT_VALID_PREFIX,
            ROOT_BUILD_SUPPORT_ROOT_ACCEPTED_PREFIX,
            ROOT_BUILD_RESIDUAL_PREFIX,
            ROOT_BUILD_RESIDUAL_DEPTH_PREFIX,
            ROOT_BUILD_RESIDUAL_SIZE_PREFIX,
            ROOT_BUILD_GREEDY_FRONTIER_PREFIX,
            ROOT_BUILD_GREEDY_PIVOT_RANK_PREFIX,
            ROOT_BUILD_GREEDY_PIVOT_NOVELTY_PREFIX,
            ROOT_BUILD_GREEDY_PIVOT_COVERAGE_PREFIX,
            ROOT_BUILD_GREEDY_PIVOT_KIND_PREFIX,
            ROOT_BUILD_GREEDY_PIVOT_STATE_PREFIX,
            ROOT_BUILD_GREEDY_MULTIPATH_SUMMARY_PREFIX,
            ROOT_BUILD_GREEDY_PATH_PREFIX,
            STRAN2_CEX_PREFIX, STRAN2_INITIAL_SCORR_PREFIX,
            STRAN2_PLACEMENT_PREFIX,
            STRAN2_SIGNATURE_PREFIX, STRAN2_SIGNATURE_LEGACY_PREFIX,
            STRAN2_TEACHING_PREFIX, STRAN2_TEACHING_LEGACY_PREFIX,
        )):
            continue
        record = {key: _number(value) for key, value in _KEY_VALUE.findall(line)}
        schema = record.pop("schema", None)
        if isinstance(schema, int):
            schemas.append(schema)
        if DIAG_PREFIX in line:
            phase_match = re.search(r"phase=(comb|seq)(?: |$)", line)
            family_match = re.search(
                r"family=(root|gate|reject|time|mffc-work|mffc-origin)(?: |$)", line
            )
            if schema not in (9, 10) or not phase_match or not family_match:
                raise ValueError("Malformed diagnosis header")
            phase, family = phase_match[1], family_match[1]
            bucket = record.get("bucket")
            buckets, keys = DIAG_SPEC[family]
            if bucket not in buckets or any(key not in record for key in keys):
                raise ValueError("Incomplete diagnosis record")
            if any(record[key] < 0 for key in keys):
                raise ValueError("Negative diagnosis measurement")
            if family == "root":
                if (
                    record["valid"] != record["nonpositive"] + record["positive"]
                    or record["positive"] != record["duplicate"] + record["accepted"]
                    or record["next"] != record["valid"] + record["collapsed"]
                        + record["invalid"] + record["exhausted"]
                    or record["started"] > record["roots"]
                    or record["raw"] < record["valid"] + record["collapsed"]
                ):
                    raise ValueError("Diagnosis root accounting mismatch")
            for destination in (phase, "all"):
                for key in keys:
                    field = (
                        f"diag_{destination}_{family.replace('-', '_')}_"
                        f"{bucket}_{key.replace('-', '_')}"
                    )
                    diagnosis[field] = diagnosis.get(field, 0) + record[key]
        elif STRICT_GUIDE_PREFIX in line:
            strict_guide_records.append(record)
        elif STRICT_CEX_PREFIX in line:
            strict_cex_records.append(record)
        elif SIGNATURE_GUIDE_PREFIX in line:
            signature_guide_records.append(record)
        elif STRAN2_INITIAL_SCORR_PREFIX in line:
            stran2_initial_scorr_records.append(record)
        elif STRAN2_CEX_PREFIX in line:
            retained = re.search(r"(?:^| )retained=(\d+)/(\d+)(?: |$)", line)
            if retained:
                record["retained"] = int(retained.group(1))
                record["capacity"] = int(retained.group(2))
            stran2_cex_records.append(record)
        elif STRAN2_PLACEMENT_PREFIX in line:
            record["mode-root-batch"] = int("mode=root-batch" in line)
            record["mode-direct"] = int("mode=direct" in line)
            stran2_placement_records.append(record)
        elif (STRAN2_SIGNATURE_PREFIX in line or
              STRAN2_SIGNATURE_LEGACY_PREFIX in line):
            stran2_signature_records.append(record)
        elif (STRAN2_TEACHING_PREFIX in line or
              STRAN2_TEACHING_LEGACY_PREFIX in line):
            stran2_teaching_records.append(record)
        elif TIME_PREFIX in line:
            time_records.append(record)
        elif BUILD_PREFIX in line:
            build_records.append(record)
        elif ROOT_TIME_PREFIX in line:
            root_time_records.append(record)
            if "scope=closure " in line:
                closure_times.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_time_records[phase.group(1)].append(record)
            time_records.append(_root_time_to_legacy(record))
        elif ROOT_PREPROCESS_DETAIL_PREFIX in line:
            root_preprocess_detail_records.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_preprocess_detail_records[
                    phase.group(1)
                ].append(record)
        elif ROOT_PAGE_REUSE_DETAIL_PREFIX in line:
            root_page_reuse_detail_records.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_page_reuse_detail_records[
                    phase.group(1)
                ].append(record)
        elif ROOT_COMMIT_PREFIX in line:
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            kind = re.search(r"(?:^| )kind=(constant|existing|build)(?: |$)", line)
            if phase and kind:
                root_commits.append((phase.group(1), kind.group(1), record))
        elif ROOT_EFFECT_PREFIX in line:
            stage = re.search(r"(?:^| )stage=(comb|seq)(?: |$)", line)
            kind = re.search(r"(?:^| )kind=(constant|existing|build)(?: |$)", line)
            if stage and kind:
                root_effects.append((stage.group(1), kind.group(1), record))
        elif ROOT_LANE_PREFIX in line:
            lane = re.search(r"(?:^| )lane=(cbs|scorr)(?: |$)", line)
            kind = re.search(r"(?:^| )kind=(constant|existing|build)(?: |$)", line)
            if lane and kind:
                root_lanes.append((lane.group(1), kind.group(1), record))
        elif ROOT_SUMMARY_PREFIX in line:
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                record["phase-id"] = 0 if phase.group(1) == "comb" else 1
            root_summaries.append(record)
            if "scope=closure " in line:
                closure_summaries.append(record)
        elif ROOT_HELPER_PREFIX in line:
            root_helpers.append(record)
        elif ROOT_PAGED_PREFIX in line or ROOT_WAVE_PREFIX in line:
            root_paged.append(record)
        elif ROOT_ITERATOR_PREFIX in line:
            root_iterators.append(record)
        elif ROOT_BUILD_HORIZON_PREFIX in line:
            root_build_horizons.append(record)
        elif ROOT_KIT_PREFIX in line:
            root_kit_records.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_kit_records[phase.group(1)].append(record)
        elif ROOT_BDC_PREFIX in line:
            root_bdc_records.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_bdc_records[phase.group(1)].append(record)
        elif ROOT_TFO_CORE_PREFIX in line:
            root_tfo_core_records.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_tfo_core_records[phase.group(1)].append(record)
        elif ROOT_ISF_TIME_PREFIX in line:
            root_isf_time_records.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_isf_time_records[phase.group(1)].append(record)
        elif ROOT_SEQ_PREFIX in line:
            root_seq.append(record)
        elif ROOT_BUILD_FUNNEL_PREFIX in line:
            root_build_funnels.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_build_funnels[phase.group(1)].append(record)
        elif ROOT_BUILD_SUPPORT_PREFIX in line:
            root_build_supports.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_build_supports[phase.group(1)].append(record)
        elif ROOT_BUILD_RESIDUAL_PREFIX in line:
            root_build_residuals.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_build_residuals[phase.group(1)].append(record)
        elif ROOT_BUILD_GREEDY_FRONTIER_PREFIX in line:
            root_build_greedy_frontiers.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_build_greedy_frontiers[phase.group(1)].append(
                    record
                )
        elif ROOT_BUILD_GREEDY_MULTIPATH_SUMMARY_PREFIX in line:
            root_build_greedy_multipath.append(record)
            phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
            if phase:
                root_phase_build_greedy_multipath[phase.group(1)].append(
                    record
                )
        elif ROOT_BUILD_GREEDY_PATH_PREFIX in line:
            rank = re.search(r"(?:^| )top-rank=([^ ]+)(?: |$)", line)
            path = record.get("path-index")
            if rank and isinstance(path, int):
                path_record = (rank.group(1), path, record)
                root_build_greedy_paths.append(path_record)
                phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
                if phase:
                    root_phase_build_greedy_paths[phase.group(1)].append(
                        path_record
                    )
        else:
            family = None
            for name, prefix in (
                ("stage", ROOT_BUILD_STAGE_PREFIX),
                ("rank", ROOT_BUILD_RANK_PREFIX),
                ("gates", ROOT_BUILD_GATES_PREFIX),
                ("gain", ROOT_BUILD_GAIN_PREFIX),
                ("ci", ROOT_BUILD_CI_PREFIX),
                ("divrank", ROOT_BUILD_DIVRANK_PREFIX),
                ("mffc", ROOT_BUILD_MFFC_PREFIX),
                ("support_size", ROOT_BUILD_SUPPORT_SIZE_PREFIX),
                ("support_mult", ROOT_BUILD_SUPPORT_MULT_PREFIX),
                ("support_stage", ROOT_BUILD_SUPPORT_STAGE_PREFIX),
                ("support_root_valid", ROOT_BUILD_SUPPORT_ROOT_VALID_PREFIX),
                ("support_root_accepted",
                 ROOT_BUILD_SUPPORT_ROOT_ACCEPTED_PREFIX),
                ("residual_depth", ROOT_BUILD_RESIDUAL_DEPTH_PREFIX),
                ("residual_size", ROOT_BUILD_RESIDUAL_SIZE_PREFIX),
                ("greedy_pivot_rank",
                 ROOT_BUILD_GREEDY_PIVOT_RANK_PREFIX),
                ("greedy_pivot_novelty",
                 ROOT_BUILD_GREEDY_PIVOT_NOVELTY_PREFIX),
                ("greedy_pivot_coverage",
                 ROOT_BUILD_GREEDY_PIVOT_COVERAGE_PREFIX),
                ("greedy_pivot_kind",
                 ROOT_BUILD_GREEDY_PIVOT_KIND_PREFIX),
                ("greedy_pivot_state",
                 ROOT_BUILD_GREEDY_PIVOT_STATE_PREFIX),
            ):
                if prefix in line:
                    family = name
                    break
            bucket = re.search(r"(?:^| )bucket=([^ ]+)(?: |$)", line)
            if family and bucket:
                root_build_buckets[family].append((bucket.group(1), record))
                phase = re.search(r"(?:^| )phase=(comb|seq)(?: |$)", line)
                if phase:
                    root_phase_build_buckets[phase.group(1)][family].append(
                        (bucket.group(1), record)
                    )
    if root_effects or root_lanes or root_summaries:
        build_records.append(
            _root_effect_to_build(root_effects, root_lanes, root_summaries)
        )
    result.update(_root_effect_matrix(root_effects))
    result.update(_root_lane_matrix(root_lanes))
    result.update(_root_summary_stage_gains(root_summaries))

    def sum_field(records: list[dict[str, int | float]], key: str) -> Any:
        values = [record[key] for record in records if key in record]
        return sum(values) if values else NA

    def max_field(records: list[dict[str, int | float]], key: str) -> Any:
        values = [record[key] for record in records if key in record]
        return max(values) if values else NA

    def sum_alias(records: list[dict[str, int | float]], *keys: str) -> Any:
        values = []
        for record in records:
            for key in keys:
                if key in record:
                    values.append(record[key])
                    break
        return sum(values) if values else NA

    result.update({
        "signature_guide_records": len(signature_guide_records) or NA,
        "signature_guide_mode": max_field(signature_guide_records, "mode"),
        "signature_guide_slots_max": max_field(signature_guide_records, "slots-max"),
        **{f"signature_guide_{key.replace('-', '_')}":
           sum_field(signature_guide_records, key) for key in SIGNATURE_GUIDE_KEYS},
    })

    result.update({
        "strict_guide_records": len(strict_guide_records) or NA,
        **{f"strict_guide_{key.replace('-', '_')}":
           sum_field(strict_guide_records, key) for key in STRICT_GUIDE_KEYS},
    })

    # The strict bank spans epochs: these are cumulative counters, not per-
    # epoch increments. Summing records would count the same traces repeatedly.
    strict_last = strict_cex_records[-1] if strict_cex_records else {}
    result.update({
        "strict_cex_records": len(strict_cex_records) or NA,
        **{f"strict_cex_{key.replace('-', '_')}": strict_last.get(key, NA)
           for key in STRICT_CEX_KEYS},
    })

    result.update({
        "stran2_initial_scorr_records": (
            len(stran2_initial_scorr_records)
            if stran2_initial_scorr_records else NA),
        **{
            f"stran2_initial_scorr_{key.replace('-', '_')}":
                (stran2_initial_scorr_records[-1].get(key, NA)
                 if stran2_initial_scorr_records else NA)
            for key in (
                "frames", "conflict-limit", "source-and", "result-and",
                "source-reg", "result-reg", "completed", "rounds",
                "bmc-unsat", "bmc-sat", "bmc-unknown", "induction-unsat",
                "induction-sat", "induction-unknown", "conflicts",
                "total-sec", "bmc-sec", "induction-sec", "reduce-sec",
            )
        },
        "stran2_cex_records": (
            len(stran2_cex_records) if stran2_cex_records else NA),
        "stran2_cex_retained": sum_field(stran2_cex_records, "retained"),
        "stran2_cex_capacity": max_field(stran2_cex_records, "capacity"),
        "stran2_cex_packed_lanes_seen": sum_field(
            stran2_cex_records, "packed-lanes-seen"),
        "stran2_cex_duplicates": sum_field(stran2_cex_records, "duplicates"),
        "stran2_cex_ignored_induction": sum_field(
            stran2_cex_records, "ignored-induction"),
        "stran2_cex_too_long": sum_field(stran2_cex_records, "too-long"),
        "stran2_cex_words": max_field(stran2_cex_records, "words"),
        "stran2_placement_records": (
            len(stran2_placement_records) if stran2_placement_records else NA),
        "stran2_placement_direct_records": sum_field(
            stran2_placement_records, "mode-direct"),
        "stran2_placement_root_batch_records": sum_field(
            stran2_placement_records, "mode-root-batch"),
        "stran2_trace_budget_max": max_field(
            stran2_placement_records, "trace-budget"),
        "stran2_random_fill_max": max_field(
            stran2_placement_records, "random-fill"),
        "stran2_overflow_max": max_field(
            stran2_placement_records, "overflow"),
        "stran2_signature_records": (
            len(stran2_signature_records) if stran2_signature_records else NA),
        "stran2_signature_source_words_max": max_field(
            stran2_signature_records, "source-words"),
        "stran2_signature_random_words_max": max_field(
            stran2_signature_records, "random-words"),
        "stran2_signature_build_words_max": max_field(
            stran2_signature_records, "build-words"),
        "stran2_signature_frames_max": max_field(
            stran2_signature_records, "frames"),
        "stran2_signature_source_slots_max": max_field(
            stran2_signature_records, "source-slots"),
        "stran2_signature_build_slots_max": max_field(
            stran2_signature_records, "build-slots"),
        "stran2_signature_reachable_cex_max": max_field(
            stran2_signature_records, "reachable-cex"),
        "stran2_signature_cex_capacity_max": max_field(
            stran2_signature_records, "cex-capacity"),
        "stran2_teaching_records": (
            len(stran2_teaching_records) if stran2_teaching_records else NA),
        "stran2_teaching_root_signatures": sum_field(
            stran2_teaching_records, "root-signatures"),
        "stran2_teaching_selector_calls": sum_field(
            stran2_teaching_records, "selector-calls"),
        "stran2_teaching_roots_with_cex": sum_field(
            stran2_teaching_records, "roots-with-cex"),
        "stran2_teaching_selected_cex": sum_field(
            stran2_teaching_records, "selected-cex-traces")
            if any("selected-cex-traces" in record
                   for record in stran2_teaching_records)
            else sum_field(stran2_teaching_records, "selected-cex"),
        "stran2_teaching_distinguishable_proxies": sum_field(
            stran2_teaching_records, "distinguishable-proxies"),
        "stran2_teaching_covered_proxies": sum_field(
            stran2_teaching_records, "covered-proxies"),
        "stran2_teaching_selection_and_gather_sec": sum_field(
            stran2_teaching_records, "selection-and-gather"),
    })

    result.update({
        "root_helper_retained_max": max_field(root_helpers, "retained"),
        "root_helper_injected_events": sum_alias(
            root_helpers, "injected-events", "active-events"),
        "root_helper_inactive_events": sum_alias(
            root_helpers, "inactive-events", "dormant-events"),
        # Compatibility aliases for existing CSV consumers.
        "root_helper_active_events": sum_alias(
            root_helpers, "injected-events", "active-events"),
        "root_helper_dormant_events": sum_alias(
            root_helpers, "inactive-events", "dormant-events"),
        "root_helper_dedup": sum_field(root_helpers, "dedup"),
        "root_helper_invalidated": sum_field(root_helpers, "invalidated"),
        "root_helper_classes": sum_field(root_helpers, "classes"),
        "root_helper_endpoints_max": max_field(root_helpers, "endpoints-max"),
        "root_helper_materialized_gates": sum_field(
            root_helpers, "materialized-gates"),
        "root_batch_relations_max": max_field(root_helpers, "batch-relations-max"),
        "root_srm_nodes_max": max_field(root_helpers, "srm-nodes-max"),
        "root_new_proved": sum_field(root_paged, "new-proved"),
        "root_history_proved_selected": sum_field(
            root_paged, "history-proved-selected"),
        "root_proof_waves": sum_alias(root_paged, "waves", "pages"),
        "root_wave_continuations": sum_field(root_paged, "continuations"),
        # Compatibility aliases for schema-3 CSV readers.
        "root_proof_pages": sum_alias(root_paged, "waves", "pages"),
        "root_page_continuations": sum_field(root_paged, "continuations"),
        "root_seq_obligations": sum_field(root_seq, "candidates"),
        "root_seq_seeded": sum_field(root_seq, "seeded"),
        "root_seq_helper_seeds": sum_alias(
            root_seq, "helper-seeds", "comb-helper-seeds"),
        "root_seq_proved": sum_field(root_seq, "proved"),
        "root_seq_split": sum_field(root_seq, "split"),
        "root_seq_unknown": sum_field(root_seq, "unknown"),
        "root_iterator_initialized": sum_field(root_iterators, "initialized"),
        "root_iterator_next": sum_field(root_iterators, "next"),
        "root_iterator_exhausted": sum_field(root_iterators, "exhausted"),
        "root_iterator_q_wave_stops": sum_alias(
            root_iterators, "q-wave-stops", "q-page-stops"),
        "root_iterator_q_page_stops": sum_alias(
            root_iterators, "q-wave-stops", "q-page-stops"),
        "root_iterator_snapshot_discarded": sum_field(
            root_iterators, "snapshot-discarded"),
        "root_iterator_live_max": max_field(root_iterators, "live-max"),
        "root_iterator_live_final": sum_field(root_iterators, "live-final"),
        "root_iterator_invalid": sum_field(root_iterators, "invalid"),
    })

    horizon_eligible = sum_field(root_build_horizons, "eligible-roots")
    horizon_capacity = sum_field(root_build_horizons, "q-slot-capacity")
    horizon_used = sum_field(root_build_horizons, "q-slots-used")
    horizon_at_q = sum_field(root_build_horizons, "at-q-roots")
    horizon_exhausted = sum_field(
        root_build_horizons, "exhausted-before-q-roots")
    horizon_zero = sum_field(root_build_horizons, "zero-accepted-roots")
    result.update({
        "root_build_horizon_records": (
            len(root_build_horizons) if root_build_horizons else NA),
        "root_build_horizon_q_limit_max": max_field(
            root_build_horizons, "q-limit"),
        "root_build_horizon_eligible_roots": horizon_eligible,
        "root_build_horizon_q_slot_capacity": horizon_capacity,
        "root_build_horizon_q_slots_used": horizon_used,
        "root_build_horizon_at_q_roots": horizon_at_q,
        "root_build_horizon_exhausted_before_q_roots": horizon_exhausted,
        "root_build_horizon_unfinished_below_q_roots": sum_field(
            root_build_horizons, "unfinished-below-q-roots"),
        "root_build_horizon_zero_accepted_roots": horizon_zero,
        "root_build_horizon_accepted_total": sum_field(
            root_build_horizons, "accepted-total"),
        "root_build_horizon_accepted_max_per_root": max_field(
            root_build_horizons, "accepted-max-per-root"),
        "root_build_horizon_q_slot_utilization_pct": _ratio(
            horizon_used, horizon_capacity),
        "root_build_horizon_at_q_rate_pct": _ratio(
            horizon_at_q, horizon_eligible),
        "root_build_horizon_exhausted_before_q_rate_pct": _ratio(
            horizon_exhausted, horizon_eligible),
        "root_build_horizon_zero_accepted_rate_pct": _ratio(
            horizon_zero, horizon_eligible),
    })

    for key in ROOT_KIT_KEYS:
        aggregate = max_field if key == "core-max" else sum_field
        result[f"root_kit_{_field_token(key)}"] = aggregate(
            root_kit_records, key)
        for phase in ("comb", "seq"):
            result[f"root_{phase}_kit_{_field_token(key)}"] = aggregate(
                root_phase_kit_records[phase], key)
        result[f"root_bdc_{_field_token(key)}"] = aggregate(
            root_bdc_records, key)
        for phase in ("comb", "seq"):
            result[f"root_{phase}_bdc_{_field_token(key)}"] = aggregate(
                root_phase_bdc_records[phase], key)

    for key in ROOT_TFO_CORE_KEYS:
        result[f"root_tfo_core_{_field_token(key)}"] = sum_field(
            root_tfo_core_records, key)
        for phase in ("comb", "seq"):
            result[f"root_{phase}_tfo_core_{_field_token(key)}"] = sum_field(
                root_phase_tfo_core_records[phase], key)

    for key in ROOT_ISF_TIME_KEYS:
        result[f"root_isf_{_field_token(key)}"] = sum_field(
            root_isf_time_records, key)
        for phase in ("comb", "seq"):
            result[f"root_{phase}_isf_{_field_token(key)}"] = sum_field(
                root_phase_isf_time_records[phase], key)

    funnel_max = {"reservoir-max", "pool-max", "mffc-max"}
    for key in (
        "reservoir-calls", "reservoir-nodes", "reservoir-max",
        "pool-nodes", "pool-max", "pool-empty", "mffc-sum", "mffc-max",
        "mffc-one-skipped", "iterator-next", "semantic-invalid", "collapsed-direct",
        "reject-nonpositive", "reject-known", "reject-direct", "reject-page",
        "accepted",
    ):
        field = f"root_build_{_field_token(key)}"
        result[field] = (
            max_field(root_build_funnels, key)
            if key in funnel_max else sum_field(root_build_funnels, key)
        )

    support_max = {
        "max-valid-candidates-root", "max-valid-supports-root",
        "max-accepted-candidates-root", "max-accepted-supports-root",
    }

    def populate_support_fields(
        records: list[dict[str, int | float]], field_prefix: str,
    ) -> None:
        values: dict[str, Any] = {}
        for key in ROOT_BUILD_SUPPORT_KEYS:
            values[key] = (
                max_field(records, key)
                if key in support_max else sum_field(records, key)
            )
            result[f"{field_prefix}_{_field_token(key)}"] = values[key]
        result[f"{field_prefix}_valid_candidates_per_support"] = _quotient(
            values["valid-candidates"], values["valid-supports"])
        result[f"{field_prefix}_accepted_candidates_per_support"] = _quotient(
            values["accepted-candidates"], values["accepted-supports"])
        result[f"{field_prefix}_support_accept_rate_pct"] = _ratio(
            values["accepted-supports"], values["valid-supports"])
        result[f"{field_prefix}_candidate_submit_rate_pct"] = _ratio(
            values["submitted-candidates"], values["accepted-candidates"])
        result[f"{field_prefix}_support_submit_rate_pct"] = _ratio(
            values["submitted-supports"], values["accepted-supports"])
        result[f"{field_prefix}_submitted_candidate_proof_rate_pct"] = _ratio(
            values["proved-candidates"], values["submitted-candidates"])
        result[f"{field_prefix}_submitted_candidate_refute_rate_pct"] = _ratio(
            values["refuted-candidates"], values["submitted-candidates"])
        result[f"{field_prefix}_submitted_candidate_unknown_rate_pct"] = _ratio(
            values["unknown-candidates"], values["submitted-candidates"])
        result[f"{field_prefix}_refuted_candidate_bmc_sat_batch_share_pct"] = _ratio(
            values["refuted-bmc-sat-batch-candidates"],
            values["refuted-candidates"])
        result[f"{field_prefix}_refuted_candidate_ind_only_sat_batch_share_pct"] = _ratio(
            values["refuted-ind-only-sat-batch-candidates"],
            values["refuted-candidates"])
        result[f"{field_prefix}_refuted_candidate_no_sat_batch_share_pct"] = _ratio(
            values["refuted-no-sat-batch-candidates"],
            values["refuted-candidates"])
        result[f"{field_prefix}_submitted_support_proof_rate_pct"] = _ratio(
            values["proved-supports"], values["submitted-supports"])
        result[f"{field_prefix}_submitted_support_no_proof_rate_pct"] = _ratio(
            values["submitted-no-proof-supports"],
            values["submitted-supports"])
        result[f"{field_prefix}_support_prove_rate_pct"] = _ratio(
            values["proved-supports"], values["accepted-supports"])
        result[f"{field_prefix}_support_select_rate_pct"] = _ratio(
            values["selected-with-accepted-supports"],
            values["accepted-supports"])
        proved_min = values["proved-min-gate-supports"]
        proved_above = values["proved-only-above-min-supports"]
        selected_min = values["selected-min-gate-supports"]
        selected_above = values["selected-only-above-min-supports"]
        selected_below = values["selected-below-accepted-min-supports"]
        proved_current = (
            proved_min + proved_above
            if all(isinstance(value, (int, float))
                   for value in (proved_min, proved_above)) else NA
        )
        selected_current = (
            selected_min + selected_above + selected_below
            if all(isinstance(value, (int, float))
                   for value in (selected_min, selected_above,
                                 selected_below)) else NA
        )
        result[f"{field_prefix}_proved_min_gate_share_pct"] = _ratio(
            proved_min, proved_current)
        result[f"{field_prefix}_selected_min_gate_share_pct"] = _ratio(
            selected_min, selected_current)
        result[f"{field_prefix}_accepted_gate_excess_per_candidate"] = (
            _quotient(values["accepted-gate-excess"],
                      values["accepted-candidates"])
        )

    populate_support_fields(root_build_supports, "root_build_support")

    def populate_residual_fields(
        records: list[dict[str, int | float]], field_prefix: str,
    ) -> None:
        values: dict[str, Any] = {}
        for key in ROOT_BUILD_RESIDUAL_KEYS:
            values[key] = (
                max_field(records, key)
                if key == "sample-rate" else sum_field(records, key)
            )
            result[f"{field_prefix}_{_field_token(key)}"] = values[key]
        result[f"{field_prefix}_sampled_root_rate_pct"] = _ratio(
            values["sampled-roots"], values["eligible-roots"])
        result[f"{field_prefix}_no_pair_root_rate_pct"] = _ratio(
            values["no-pair-roots"], values["sampled-roots"])
        pair_roots = (
            values["sampled-roots"] - values["no-pair-roots"]
            if all(isinstance(value, (int, float)) for value in (
                values["sampled-roots"], values["no-pair-roots"]))
            else NA
        )
        result[f"{field_prefix}_static_complete_rate_pct"] = _ratio(
            values["static-complete-roots"], pair_roots)
        result[f"{field_prefix}_greedy_complete_rate_pct"] = _ratio(
            values["greedy-complete-roots"], pair_roots)
        result[f"{field_prefix}_static_average_cover_size"] = _quotient(
            values["static-cover-size-sum"],
            values["static-complete-roots"])
        result[f"{field_prefix}_greedy_average_cover_size"] = _quotient(
            values["greedy-cover-size-sum"],
            values["greedy-complete-roots"])

    populate_residual_fields(root_build_residuals, "root_build_residual")

    def populate_greedy_frontier_fields(
        records: list[dict[str, int | float]], field_prefix: str,
    ) -> None:
        values: dict[str, Any] = {}
        for key in ROOT_BUILD_GREEDY_FRONTIER_KEYS:
            values[key] = (
                max_field(records, key)
                if key == "frontier-max" else sum_field(records, key)
            )
            result[f"{field_prefix}_{_field_token(key)}"] = values[key]
        result[f"{field_prefix}_average_frontier_size"] = _quotient(
            values["pivots"], values["roots"])
        result[f"{field_prefix}_unique_state_rate_pct"] = _ratio(
            values["unique-states"], values["pivots"])
        result[f"{field_prefix}_duplicate_state_rate_pct"] = _ratio(
            values["duplicate-states"], values["pivots"])
        result[f"{field_prefix}_zero_novel_rate_pct"] = _ratio(
            values["zero-novel"], values["pivots"])
        result[f"{field_prefix}_novel_cover_share_pct"] = _ratio(
            values["novel-sum"], values["cover-sum"])
        result[f"{field_prefix}_attempted_frontier_share_pct"] = _ratio(
            values["attempts"], values["pivots"])
        result[f"{field_prefix}_pivot_found_rate_pct"] = _ratio(
            values["found"], values["attempts"])
        result[f"{field_prefix}_time_per_attempt_sec"] = _quotient(
            values["time-sec"], values["attempts"])
        result[f"{field_prefix}_cache_hit_rate_pct"] = _ratio(
            values["cache-hits"], values["cache-lookups"])
        result[f"{field_prefix}_cache_cross_page_hit_share_pct"] = _ratio(
            values["cache-cross-page-hits"], values["cache-hits"])
        result[f"{field_prefix}_cache_fail_hit_share_pct"] = _ratio(
            values["cache-fail-hits"], values["cache-hits"])
        result[f"{field_prefix}_cache_saved_over_lookup"] = _quotient(
            values["cache-saved-sec"], values["cache-lookup-sec"])
        result[f"{field_prefix}_recursive_duplicate_rate_pct"] = _ratio(
            values["recursive-duplicates"], values["recursive-calls"])
        result[f"{field_prefix}_recursive_fail_hit_rate_pct"] = _ratio(
            values["recursive-fail-hits"], values["recursive-duplicates"])
        result[f"{field_prefix}_recursive_cross_page_share_pct"] = _ratio(
            values["recursive-cross-page"], values["recursive-duplicates"])
        result[f"{field_prefix}_recursive_saved_over_lookup"] = _quotient(
            values["recursive-saved-sec"], values["recursive-lookup-sec"])

    populate_greedy_frontier_fields(
        root_build_greedy_frontiers,
        "root_build_greedy_frontier",
    )

    def populate_greedy_multipath_fields(
        records: list[dict[str, int | float]], field_prefix: str,
    ) -> None:
        values = {
            key: sum_field(records, key)
            for key in ROOT_BUILD_GREEDY_MULTIPATH_KEYS
        }
        for key, value in values.items():
            result[f"{field_prefix}_{_field_token(key)}"] = value
        result[f"{field_prefix}_cache_hit_rate_pct"] = _ratio(
            values["cache-hits"], values["cache-lookups"])
        result[f"{field_prefix}_cache_fail_hit_share_pct"] = _ratio(
            values["cache-fail-hits"], values["cache-hits"])
        result[f"{field_prefix}_duplicate_per_extra_accepted"] = _quotient(
            values["duplicate-candidate-fingerprints"],
            values["extra-accepted"])
        result[f"{field_prefix}_extra_q_slot_rate_pct"] = _ratio(
            values["extra-q-slots"], values["extra-accepted"])

    def populate_greedy_path_fields(
        records: list[tuple[str, int, dict[str, int | float]]],
        field_prefix: str,
    ) -> None:
        for rank in ROOT_BUILD_GREEDY_PATH_RANKS:
            for path in ROOT_BUILD_GREEDY_PATH_INDICES:
                cell_records = [
                    record
                    for record_rank, record_path, record in records
                    if record_rank == rank and record_path == path
                ]
                for metric in ROOT_BUILD_GREEDY_PATH_METRICS:
                    field = (
                        f"{field_prefix}_rank_{_field_token(rank)}_"
                        f"path_{path}_{_field_token(metric)}"
                    )
                    result[field] = sum_field(cell_records, metric)

    populate_greedy_multipath_fields(
        root_build_greedy_multipath,
        "root_build_greedy_multipath",
    )
    populate_greedy_path_fields(
        root_build_greedy_paths,
        "root_build_greedy_path",
    )
    for family, (buckets, metrics) in ROOT_BUILD_BUCKETS.items():
        for bucket in buckets:
            records = [
                record for record_bucket, record in root_build_buckets[family]
                if record_bucket == bucket
            ]
            for metric in metrics:
                field = (
                    f"root_build_{family}_{_field_token(bucket)}_"
                    f"{_field_token(metric)}"
                )
                result[field] = sum_field(records, metric)

    for phase in ("comb", "seq"):
        phase_funnels = root_phase_build_funnels[phase]
        for key in (
            "reservoir-calls", "reservoir-nodes", "reservoir-max",
            "pool-nodes", "pool-max", "pool-empty", "mffc-sum", "mffc-max",
            "mffc-one-skipped", "iterator-next", "semantic-invalid",
            "collapsed-direct", "reject-nonpositive", "reject-known",
            "reject-direct", "reject-page", "accepted",
        ):
            field = f"root_{phase}_build_{_field_token(key)}"
            result[field] = (
                max_field(phase_funnels, key)
                if key in funnel_max else sum_field(phase_funnels, key)
            )
        populate_support_fields(
            root_phase_build_supports[phase],
            f"root_{phase}_build_support",
        )
        populate_residual_fields(
            root_phase_build_residuals[phase],
            f"root_{phase}_build_residual",
        )
        populate_greedy_frontier_fields(
            root_phase_build_greedy_frontiers[phase],
            f"root_{phase}_build_greedy_frontier",
        )
        populate_greedy_multipath_fields(
            root_phase_build_greedy_multipath[phase],
            f"root_{phase}_build_greedy_multipath",
        )
        populate_greedy_path_fields(
            root_phase_build_greedy_paths[phase],
            f"root_{phase}_build_greedy_path",
        )
        for family, (buckets, metrics) in ROOT_BUILD_BUCKETS.items():
            for bucket in buckets:
                records = [
                    record for record_bucket, record
                    in root_phase_build_buckets[phase][family]
                    if record_bucket == bucket
                ]
                for metric in metrics:
                    field = (
                        f"root_{phase}_build_{family}_{_field_token(bucket)}_"
                        f"{_field_token(metric)}"
                    )
                    result[field] = sum_field(records, metric)

    result.update(diagnosis)
    if diagnosis:
        for phase in ("comb", "seq"):
            for family, (buckets, keys) in DIAG_SPEC.items():
                fields = [
                    f"diag_{phase}_{family.replace('-', '_')}_{bucket}_{key.replace('-', '_')}"
                    for bucket in buckets
                    for key in keys
                ]
                if any(field in diagnosis for field in fields) and not all(
                    field in diagnosis for field in fields
                ):
                    raise ValueError("Missing diagnosis bucket")
        roots = [diagnosis.get(f"diag_all_root_{bucket}_roots") for bucket in range(8)]
        eligible = result["root_build_horizon_eligible_roots"]
        if (
            all(value is not None for value in roots)
            and eligible != NA
            and sum(roots) != eligible
        ):
            raise ValueError("Diagnosis eligible root mismatch")
    if schemas:
        result["profile_schema"] = max(schemas)
    result["profile_time_records"] = len(time_records) if time_records else NA
    result["profile_seq_build_records"] = len(build_records) if build_records else NA

    root_times = _sum_records(root_time_records, ROOT_TIME_KEYS)
    for key, value in root_times.items():
        field = f"profile_{key.replace('-', '_')}"
        if field in result:
            result[field] = value

    for key, value in _sum_records(
        root_preprocess_detail_records, ROOT_PREPROCESS_DETAIL_KEYS
    ).items():
        result[f"root_preprocess_{key.replace('-', '_')}"] = value

    for phase in ("comb", "seq"):
        for key, value in _sum_records(
            root_phase_preprocess_detail_records[phase],
            ROOT_PREPROCESS_DETAIL_KEYS,
        ).items():
            result[
                f"root_{phase}_preprocess_{key.replace('-', '_')}"
            ] = value

    for key, value in _sum_records(
        root_page_reuse_detail_records, ROOT_PAGE_REUSE_DETAIL_KEYS
    ).items():
        result[f"root_page_reuse_{key.replace('-', '_')}"] = value

    for phase in ("comb", "seq"):
        for key, value in _sum_records(
            root_phase_page_reuse_detail_records[phase],
            ROOT_PAGE_REUSE_DETAIL_KEYS,
        ).items():
            result[
                f"root_{phase}_page_reuse_{key.replace('-', '_')}"
            ] = value

    for phase in ("comb", "seq"):
        for key, value in _sum_records(
            root_phase_time_records[phase], ROOT_TIME_KEYS
        ).items():
            result[f"{phase}_profile_{key.replace('-', '_')}"] = value
        phase_legacy_times = [
            _root_time_to_legacy(record)
            for record in root_phase_time_records[phase]
        ]
        for key, value in _sum_records(phase_legacy_times, TIME_KEYS).items():
            result[f"{phase}_profile_{key.replace('-', '_')}"] = value

    times = _sum_records(time_records, TIME_KEYS)
    for key, value in times.items():
        field = (
            "profile_overhead_sec" if key == "profile-overhead-sec"
            else f"profile_{key.replace('-', '_')}"
        )
        result[field] = value

    build = _sum_records(build_records, BUILD_KEYS)
    for key, value in build.items():
        field = (
            key.replace("-", "_")
            if key.startswith(("seq-build-", "seq-total-", "seq-direct-",
                               "seq-interaction-", "final-"))
            else f"seq_build_{key.replace('-', '_')}"
        )
        result[field] = value

    if root_commits:
        # Schema 8 accounts for each disjoint commit once, including closure.
        # The original stage matrix continues to describe proof origin.
        result["profile_closure_records"] = len(closure_times)
        result["profile_closure_sec"] = sum(r["total-sec"] for r in closure_times)
        result["profile_closure_and_gain"] = sum(r["final-and-gain"] for r in closure_summaries)
        result["profile_closure_selected"] = sum(r["selected-roots"] for r in closure_summaries)
        if (len(root_commits) != 3 * len(root_summaries)
                or len(root_time_records) != len(root_summaries)
                or len(closure_times) != len(closure_summaries)):
            raise ValueError("Incomplete commit-kind profiling records")
        previous_after = None
        for record in root_summaries:
            before, after = record["and-before"], record["and-after"]
            if (previous_after is not None and before != previous_after) or before - after != record["final-and-gain"]:
                raise ValueError("Nonconserving commit profile boundaries")
            previous_after = after
        for phase in ("comb", "seq"):
            marginal = 0
            for kind in ("constant", "existing", "build"):
                records = [r for p, k, r in root_commits if p == phase and k == kind]
                for metric, key in (("selected", "selected"), ("and_gain", "marginal-and"), ("reg_gain", "marginal-reg")):
                    result[f"{phase}_commit_{kind}_{metric}"] = sum(r[key] for r in records)
                marginal += result[f"{phase}_commit_{kind}_and_gain"]
            phase_summaries = [r for r in root_summaries if r.get("phase-id") == (phase == "seq")]
            exact = sum(r["final-and-gain"] for r in phase_summaries)
            selected = sum(result[f"{phase}_commit_{k}_selected"] for k in ("constant", "existing", "build"))
            if marginal > exact or selected != sum(r["selected-roots"] for r in phase_summaries):
                raise ValueError("Nonconserving commit-kind attribution")
            result[f"{phase}_commit_cleanup_extra_and_gain"] = exact - marginal
        for metric in ("and", "reg"):
            result[f"seq_build_ordered_{metric}_gain"] = result[f"seq_commit_build_{metric}_gain"]
            result[f"seq_total_{metric}_gain"] = result[f"seq_stage_{metric}_gain"]
        result["profile_accounting_complete"] = 1

    total = result["profile_total_sec"]
    result["stran2_teaching_selection_pct_of_profile"] = _ratio(
        result["stran2_teaching_selection_and_gather_sec"], total)
    for field in (
        "build_discovery", "seq_proof_shared", "selection", "stage_eval",
        "contribution_eval", "commit", "decision", "overhead", "unprofiled",
    ):
        result[f"profile_{field}_pct"] = _ratio(
            result[f"profile_{field}_sec"], total)

    comb_proved = result["seq_build_comb_proved"]
    seq_proved = result["seq_build_seq_proved"]
    comb_selected = result["seq_build_comb_selected"]
    seq_selected = result["seq_build_seq_selected"]
    if all(isinstance(value, (int, float)) for value in (comb_proved, seq_proved)):
        result["seq_build_total_proved"] = comb_proved + seq_proved
    if all(isinstance(value, (int, float)) for value in (comb_selected, seq_selected)):
        result["seq_build_total_selected"] = comb_selected + seq_selected
    result["seq_build_proof_rate_pct"] = _ratio(
        result["seq_build_total_proved"], result["seq_build_submitted"])
    result["seq_build_seq_fraction_pct"] = _ratio(
        seq_proved, result["seq_build_total_proved"])
    result["seq_build_seq_selected_rate_pct"] = _ratio(seq_selected, seq_proved)
    result["seq_build_ordered_seq_gain_share_pct"] = _ratio(
        result["seq_build_ordered_and_gain"], result["seq_total_and_gain"])
    result["seq_build_only_seq_gain_share_pct"] = _ratio(
        result["seq_build_only_and_gain"], result["seq_total_and_gain"])
    result["seq_build_ordered_final_gain_share_pct"] = _ratio(
        result["seq_build_ordered_and_gain"], result["final_and_gain"])

    build_search = result["profile_build_discovery_sec"]
    shared_proof = result["profile_seq_proof_shared_sec"]
    if isinstance(build_search, (int, float)) and isinstance(shared_proof, (int, float)):
        upper = build_search + shared_proof
        result["seq_build_path_upper_bound_sec"] = round(upper, 9)
        result["seq_build_path_upper_bound_pct"] = _ratio(upper, total)
        gain = result["seq_build_ordered_and_gain"]
        if isinstance(gain, (int, float)) and upper > 0:
            result["seq_build_ordered_gain_per_upper_bound_sec"] = round(
                gain / upper, 6)
    return result


def validate_profile_accounting(result: dict[str, Any], final_and: int) -> None:
    """Check the profiled commit chain against the independently written AIG."""
    if result.get("profile_accounting_complete") != 1:
        return
    before = result["comb_stage_and_before"]
    gain = result["comb_stage_and_gain"] + result["seq_stage_and_gain"]
    if before - final_and != gain or result["seq_stage_and_after"] != final_and:
        raise ValueError("Final AIG disagrees with complete commit profile")
