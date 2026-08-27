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
ROOT_EFFECT_PREFIX = "stran-root experiment-effect profile:"
ROOT_LANE_PREFIX = "stran-root experiment-proof-lane profile:"
ROOT_SUMMARY_PREFIX = "stran-root experiment-summary profile:"
ROOT_HELPER_PREFIX = "stran-root helper history:"
ROOT_PAGED_PREFIX = "stran-root paged portfolio:"
ROOT_WAVE_PREFIX = "stran-root wave portfolio:"
ROOT_ITERATOR_PREFIX = "stran-root resub iterator:"
ROOT_SEQ_PREFIX = "stran-root sequential relations:"
ROOT_BUILD_FUNNEL_PREFIX = "stran-root build-funnel profile:"
ROOT_BUILD_STAGE_PREFIX = "stran-root build-stage profile:"
ROOT_BUILD_RANK_PREFIX = "stran-root build-rank profile:"
ROOT_BUILD_GATES_PREFIX = "stran-root build-gates profile:"
ROOT_BUILD_GAIN_PREFIX = "stran-root build-gain profile:"
ROOT_BUILD_CI_PREFIX = "stran-root build-ci profile:"
ROOT_BUILD_DIVRANK_PREFIX = "stran-root build-divrank profile:"
ROOT_BUILD_MFFC_PREFIX = "stran-root build-mffc profile:"

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
    "cbs-graph-sec", "cbs-screen-sec", "cbs-solve-sec",
    "scorr-graph-sec", "scorr-bmc-sec", "scorr-induction-sec",
    "scorr-resim-sec", "scorr-other-sec", "selection-repair-sec",
    "bundle-sec", "cleanup-sec", "exact-audit-sec", "shadow-sec",
    "unprofiled-sec",
)

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
}


def _field_token(value: str) -> str:
    return value.replace("-", "_").replace("+", "plus")


ROOT_BUILD_BUCKET_FIELDS = [
    f"root_build_{family}_{_field_token(bucket)}_{_field_token(metric)}"
    for family, (buckets, metrics) in ROOT_BUILD_BUCKETS.items()
    for bucket in buckets
    for metric in metrics
]

PROFILE_FIELDS = [
    "profile_schema", "profile_time_records", "profile_seq_build_records",
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
    *ROOT_EFFECT_FIELDS,
    *ROOT_LANE_FIELDS,
    *ROOT_HISTORY_FIELDS,
    *ROOT_SEQ_FIELDS,
    *ROOT_ITERATOR_FIELDS,
    *ROOT_BUILD_FUNNEL_FIELDS,
    *ROOT_BUILD_BUCKET_FIELDS,
    *ROOT_PROFILE_FIELDS,
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
                        "resub-enum-sec")
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
            key = f"final-{metric}-gain"
            if key in record:
                field = f"{stage}_stage_{metric}_gain"
                result[field] = result.get(field, 0) + record[key]
    return result


def parse_experiment_profile(stdout: str) -> dict[str, Any]:
    """Return fixed-schema metrics from one &stran stdout string."""
    result = {field: NA for field in PROFILE_FIELDS}
    time_records: list[dict[str, int | float]] = []
    build_records: list[dict[str, int | float]] = []
    root_time_records: list[dict[str, int | float]] = []
    root_effects: list[tuple[str, str, dict[str, int | float]]] = []
    root_lanes: list[tuple[str, str, dict[str, int | float]]] = []
    root_summaries: list[dict[str, int | float]] = []
    root_helpers: list[dict[str, int | float]] = []
    root_paged: list[dict[str, int | float]] = []
    root_iterators: list[dict[str, int | float]] = []
    root_seq: list[dict[str, int | float]] = []
    root_build_funnels: list[dict[str, int | float]] = []
    root_build_buckets: dict[str, list[tuple[str, dict[str, int | float]]]] = {
        family: [] for family in ROOT_BUILD_BUCKETS
    }
    schemas: list[int] = []
    for line in stdout.splitlines():
        if not any(prefix in line for prefix in (
            TIME_PREFIX, BUILD_PREFIX, ROOT_TIME_PREFIX,
            ROOT_EFFECT_PREFIX, ROOT_LANE_PREFIX, ROOT_SUMMARY_PREFIX,
            ROOT_HELPER_PREFIX,
            ROOT_PAGED_PREFIX, ROOT_WAVE_PREFIX,
            ROOT_ITERATOR_PREFIX, ROOT_SEQ_PREFIX,
            ROOT_BUILD_FUNNEL_PREFIX, ROOT_BUILD_STAGE_PREFIX,
            ROOT_BUILD_RANK_PREFIX, ROOT_BUILD_GATES_PREFIX,
            ROOT_BUILD_GAIN_PREFIX, ROOT_BUILD_CI_PREFIX,
            ROOT_BUILD_DIVRANK_PREFIX,
            ROOT_BUILD_MFFC_PREFIX,
        )):
            continue
        record = {key: _number(value) for key, value in _KEY_VALUE.findall(line)}
        schema = record.pop("schema", None)
        if isinstance(schema, int):
            schemas.append(schema)
        if TIME_PREFIX in line:
            time_records.append(record)
        elif BUILD_PREFIX in line:
            build_records.append(record)
        elif ROOT_TIME_PREFIX in line:
            root_time_records.append(record)
            time_records.append(_root_time_to_legacy(record))
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
        elif ROOT_HELPER_PREFIX in line:
            root_helpers.append(record)
        elif ROOT_PAGED_PREFIX in line or ROOT_WAVE_PREFIX in line:
            root_paged.append(record)
        elif ROOT_ITERATOR_PREFIX in line:
            root_iterators.append(record)
        elif ROOT_SEQ_PREFIX in line:
            root_seq.append(record)
        elif ROOT_BUILD_FUNNEL_PREFIX in line:
            root_build_funnels.append(record)
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
            ):
                if prefix in line:
                    family = name
                    break
            bucket = re.search(r"(?:^| )bucket=([^ ]+)(?: |$)", line)
            if family and bucket:
                root_build_buckets[family].append((bucket.group(1), record))
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

    if schemas:
        result["profile_schema"] = max(schemas)
    result["profile_time_records"] = len(time_records) if time_records else NA
    result["profile_seq_build_records"] = len(build_records) if build_records else NA

    root_times = _sum_records(root_time_records, ROOT_TIME_KEYS)
    for key, value in root_times.items():
        field = f"profile_{key.replace('-', '_')}"
        if field in result:
            result[field] = value

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

    total = result["profile_total_sec"]
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
