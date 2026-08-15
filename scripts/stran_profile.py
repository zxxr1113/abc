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
ROOT_SUMMARY_PREFIX = "stran-root experiment-summary profile:"

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
    summaries: list[dict[str, int | float]],
) -> dict[str, int | float]:
    """Aggregate the root-only 2x3 matrix into legacy Build rollups."""
    result: dict[str, int | float] = {}
    gains: dict[tuple[str, str, str], int | float] = {}
    for stage, kind, record in effects:
        if kind == "build":
            result["generated"] = result.get("generated", 0) + record.get("generated", 0)
            result["submitted"] = result.get("submitted", 0) + record.get("submitted", 0)
            result[f"{stage}-proved"] = result.get(f"{stage}-proved", 0) + record.get("proved", 0)
            result[f"{stage}-selected"] = result.get(f"{stage}-selected", 0) + record.get("selected", 0)
        gains[(stage, kind, "and")] = gains.get((stage, kind, "and"), 0) + record.get("marginal-and", 0)
        gains[(stage, kind, "reg")] = gains.get((stage, kind, "reg"), 0) + record.get("marginal-reg", 0)
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


def parse_experiment_profile(stdout: str) -> dict[str, Any]:
    """Return fixed-schema metrics from one &stran stdout string."""
    result = {field: NA for field in PROFILE_FIELDS}
    time_records: list[dict[str, int | float]] = []
    build_records: list[dict[str, int | float]] = []
    root_time_records: list[dict[str, int | float]] = []
    root_effects: list[tuple[str, str, dict[str, int | float]]] = []
    root_summaries: list[dict[str, int | float]] = []
    schemas: list[int] = []
    for line in stdout.splitlines():
        if not any(prefix in line for prefix in (
            TIME_PREFIX, BUILD_PREFIX, ROOT_TIME_PREFIX,
            ROOT_EFFECT_PREFIX, ROOT_SUMMARY_PREFIX,
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
        elif ROOT_SUMMARY_PREFIX in line:
            root_summaries.append(record)
    if root_effects or root_summaries:
        build_records.append(_root_effect_to_build(root_effects, root_summaries))

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
