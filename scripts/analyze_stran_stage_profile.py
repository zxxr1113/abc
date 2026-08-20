#!/usr/bin/env python3
"""Create a focused per-case and overall report for &stran's two stages.

The input is the raw CSV produced by ``bench_scorr_then_stran.py``.  The
output contains one row per case and a final ``OVERALL`` row.  Candidate-kind
New profiler CSVs use ordered exact attribution: Constant, then Existing, then
Build.  Thus Build is ``G(C+E+B) - G(C+E)`` and the three gains add exactly to
the actual stage gain.  ``G(B)`` is also retained as Build-only gain.  Older
CSVs without ordered fields fall back to the legacy Shapley attribution.

All reported reduction percentages use the original input AND count as their
denominator.  A candidate-kind reduction is therefore the stage reduction
multiplied by that kind's share of the stage gain, for example::

    seq_constructed_reduction_pct
        = seq_reduction_pct * seq_constructed_gain_share_pct / 100

For root schema 3, ``proved`` means newly proved events in the current
snapshot, while ``selected`` may consume a remapped history certificate.
Consequently ``selected/proved`` can exceed 100%; the report carries
``root_history_proved_selected`` separately instead of treating this as a
profiling error.
"""

from __future__ import annotations

import argparse
import csv
import statistics
import sys
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional


NA = "N/A"
STAGES = ("comb", "seq")
KINDS = ("constant", "existing", "constructed")


BASE_FIELDS = [
    "row_type", "case", "status",
    "input_and", "after_comb_and", "after_seq_and",
    "comb_reduced_and", "comb_reduction_pct",
    "seq_reduced_and", "seq_reduction_pct",
    "total_reduced_and", "total_reduction_pct",
    "input_reg", "after_comb_reg", "after_seq_reg",
    "comb_reduced_reg", "seq_reduced_reg", "total_reduced_reg",
]
HISTORY_FIELDS = [
    "root_helper_retained_max", "root_helper_injected_events",
    "root_helper_inactive_events", "root_helper_dedup",
    "root_helper_invalidated", "root_helper_classes",
    "root_helper_endpoints_max", "root_helper_materialized_gates",
    "root_batch_relations_max", "root_srm_nodes_max",
    "root_new_proved", "root_history_proved_selected",
    "root_proof_waves", "root_wave_continuations",
]
STAGE_FIELDS = [
    f"{stage}_{metric}"
    for stage in STAGES
    for metric in ("proved", "selected", "selected_per_proved_pct")
]
ATTRIBUTION_FIELDS = [f"{stage}_gain_attribution" for stage in STAGES]
KIND_FIELDS = [
    f"{stage}_{kind}_{metric}"
    for stage in STAGES
    for kind in KINDS
    for metric in (
        "proved", "selected", "and_gain", "shapley_and_gain",
        "gain_share_pct", "reduction_pct", "reg_gain", "shapley_reg_gain",
    )
]
BUILD_ONLY_FIELDS = [
    f"{stage}_build_only_{metric}"
    for stage in STAGES
    for metric in ("and_gain", "reduction_pct", "reg_gain")
]
CONSTRUCT_FIELDS = [
    f"{stage}_constructed_{metric}"
    for stage in STAGES
    for metric in (
        "proved_gates", "selected_gates", "proved_max_gates",
        "selected_max_gates", "gates_per_selected",
    )
]
TIME_FIELDS = [
    "profile_total_sec", "profile_build_discovery_sec",
    "profile_seq_proof_shared_sec", "profile_selection_sec",
    "profile_stage_eval_sec", "profile_contribution_eval_sec",
    "profile_commit_sec", "profile_decision_sec", "profile_overhead_sec",
    "profile_unprofiled_sec",
    "profile_build_discovery_pct", "profile_seq_proof_shared_pct",
    "profile_selection_pct", "profile_stage_eval_pct",
    "profile_contribution_eval_pct", "profile_commit_pct", "profile_decision_pct",
    "profile_overhead_pct", "profile_unprofiled_pct",
    "seq_build_path_upper_bound_sec", "seq_build_path_upper_bound_pct",
    "seq_build_ordered_gain_per_upper_bound_sec",
]
OVERALL_FIELDS = [
    "valid_cases", "invalid_cases", "cases_comb_improved", "cases_seq_improved",
    "mean_case_comb_reduction_pct", "median_case_comb_reduction_pct",
    "mean_case_seq_reduction_pct", "median_case_seq_reduction_pct",
]
CSV_FIELDS = (
    BASE_FIELDS + HISTORY_FIELDS + STAGE_FIELDS + ATTRIBUTION_FIELDS + KIND_FIELDS + BUILD_ONLY_FIELDS +
    CONSTRUCT_FIELDS + TIME_FIELDS + OVERALL_FIELDS
)


def number(value: Any) -> Optional[float]:
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def integer(value: Any) -> Optional[int]:
    parsed = number(value)
    return int(parsed) if parsed is not None else None


def ratio_pct(numerator: Any, denominator: Any) -> Optional[float]:
    num, den = number(numerator), number(denominator)
    if num is None or den is None or den == 0:
        return None
    return round(100.0 * num / den, 6)


def multiplied_pct(total_pct: Any, share_pct: Any) -> Optional[float]:
    """Return ``total_pct * share_pct / 100`` with report precision."""
    total, share = number(total_pct), number(share_pct)
    if total is None or share is None:
        return None
    return round(total * share / 100.0, 6)


def first_number(row: Dict[str, str], *fields: str) -> Optional[float]:
    for field in fields:
        parsed = number(row.get(field))
        if parsed is not None:
            return parsed
    return None


def case_status(row: Dict[str, str]) -> str:
    error = row.get("error", "")
    statuses = [row.get("scorr_status", ""), row.get("stran_status", ""),
                row.get("dsec_status", "")]
    if (statuses[0] == "PASS" and statuses[1] == "PASS" and
            statuses[2] in ("PASS", "SKIP") and error in ("", NA)):
        return "PASS"
    detail = error if error not in ("", NA) else "/".join(filter(None, statuses))
    return f"INVALID: {detail}"


def clean_number(value: Optional[float], integral: bool = False) -> Any:
    if value is None:
        return ""
    return int(value) if integral else round(value, 6)


def make_case(row: Dict[str, str]) -> Dict[str, Any]:
    result: Dict[str, Any] = {field: "" for field in CSV_FIELDS}
    result.update({"row_type": "case", "case": row.get("file", ""),
                   "status": case_status(row)})
    for field in HISTORY_FIELDS:
        result[field] = clean_number(integer(row.get(field)), integral=True)

    input_and = first_number(row, "stage_and_before", "scorr_and")
    after_comb_and = first_number(row, "stage_and_after_comb")
    after_seq_and = first_number(row, "stage_and_after_scorr", "stran_and")
    comb_gain = first_number(row, "comb_stage_and_gain", "comb_and_gain")
    seq_gain = first_number(row, "seq_stage_and_gain", "scorr_incremental_and_gain")
    if comb_gain is None and input_and is not None and after_comb_and is not None:
        comb_gain = input_and - after_comb_and
    if seq_gain is None and after_comb_and is not None and after_seq_and is not None:
        seq_gain = after_comb_and - after_seq_and
    total_gain = (input_and - after_seq_and
                  if input_and is not None and after_seq_and is not None else None)

    for field, value in (
        ("input_and", input_and), ("after_comb_and", after_comb_and),
        ("after_seq_and", after_seq_and), ("comb_reduced_and", comb_gain),
        ("seq_reduced_and", seq_gain), ("total_reduced_and", total_gain),
    ):
        result[field] = clean_number(value, integral=True)
    result["comb_reduction_pct"] = clean_number(ratio_pct(comb_gain, input_and))
    # Keep both stages on the same denominator so every percentage is directly
    # comparable and the candidate-kind percentages add to the stage value.
    result["seq_reduction_pct"] = clean_number(ratio_pct(seq_gain, input_and))
    result["total_reduction_pct"] = clean_number(ratio_pct(total_gain, input_and))

    input_reg = first_number(row, "stage_reg_before", "scorr_latches")
    after_comb_reg = first_number(row, "stage_reg_after_comb")
    after_seq_reg = first_number(row, "stage_reg_after_scorr", "stran_latches")
    comb_reg_gain = first_number(row, "comb_stage_reg_gain")
    seq_reg_gain = first_number(row, "seq_stage_reg_gain")
    if comb_reg_gain is None and input_reg is not None and after_comb_reg is not None:
        comb_reg_gain = input_reg - after_comb_reg
    if seq_reg_gain is None and after_comb_reg is not None and after_seq_reg is not None:
        seq_reg_gain = after_comb_reg - after_seq_reg
    total_reg_gain = (input_reg - after_seq_reg
                      if input_reg is not None and after_seq_reg is not None else None)
    for field, value in (
        ("input_reg", input_reg), ("after_comb_reg", after_comb_reg),
        ("after_seq_reg", after_seq_reg), ("comb_reduced_reg", comb_reg_gain),
        ("seq_reduced_reg", seq_reg_gain), ("total_reduced_reg", total_reg_gain),
    ):
        result[field] = clean_number(value, integral=True)

    for stage, stage_gain in (("comb", comb_gain), ("seq", seq_gain)):
        has_ordered_gain = any(
            number(row.get(f"{stage}_{kind}_ordered_and_gain")) is not None
            for kind in ("constant", "existing", "build")
        )
        result[f"{stage}_gain_attribution"] = (
            "ordered-c-e-b" if has_ordered_gain else "shapley-fallback"
        )
        stage_reduction_pct = result[f"{stage}_reduction_pct"]
        proved_total = selected_total = 0
        have_counts = False
        for kind in KINDS:
            proved = integer(row.get(f"{stage}_{kind}_proved"))
            selected = integer(row.get(f"{stage}_{kind}_selected"))
            ordered_kind = "build" if kind == "constructed" else kind
            shapley_and_gain = number(row.get(f"{stage}_{kind}_and_gain"))
            shapley_reg_gain = number(row.get(f"{stage}_{kind}_reg_gain"))
            and_gain = first_number(
                row, f"{stage}_{ordered_kind}_ordered_and_gain",
                f"{stage}_{kind}_and_gain")
            reg_gain = first_number(
                row, f"{stage}_{ordered_kind}_ordered_reg_gain",
                f"{stage}_{kind}_reg_gain")
            result[f"{stage}_{kind}_proved"] = clean_number(proved, integral=True)
            result[f"{stage}_{kind}_selected"] = clean_number(selected, integral=True)
            result[f"{stage}_{kind}_and_gain"] = clean_number(and_gain)
            result[f"{stage}_{kind}_shapley_and_gain"] = clean_number(
                shapley_and_gain)
            result[f"{stage}_{kind}_reg_gain"] = clean_number(reg_gain)
            result[f"{stage}_{kind}_shapley_reg_gain"] = clean_number(
                shapley_reg_gain)
            gain_share_pct = ratio_pct(and_gain, stage_gain)
            result[f"{stage}_{kind}_gain_share_pct"] = clean_number(gain_share_pct)
            reduction_pct = multiplied_pct(stage_reduction_pct, gain_share_pct)
            # A zero net stage gain can contain cancelling ordered contributions,
            # in which case the share is undefined.  Direct input normalization
            # remains well-defined and is the equivalent usable fallback.
            if reduction_pct is None:
                reduction_pct = ratio_pct(and_gain, input_and)
            result[f"{stage}_{kind}_reduction_pct"] = clean_number(reduction_pct)
            if proved is not None and selected is not None:
                proved_total += proved
                selected_total += selected
                have_counts = True
        build_only_and_gain = number(row.get(f"{stage}_build_only_and_gain"))
        build_only_reg_gain = number(row.get(f"{stage}_build_only_reg_gain"))
        result[f"{stage}_build_only_and_gain"] = clean_number(build_only_and_gain)
        result[f"{stage}_build_only_reg_gain"] = clean_number(build_only_reg_gain)
        result[f"{stage}_build_only_reduction_pct"] = clean_number(
            ratio_pct(build_only_and_gain, input_and))
        if have_counts:
            result[f"{stage}_proved"] = proved_total
            result[f"{stage}_selected"] = selected_total
            result[f"{stage}_selected_per_proved_pct"] = clean_number(
                ratio_pct(selected_total, proved_total))
        for metric in ("proved_gates", "selected_gates", "proved_max_gates",
                       "selected_max_gates"):
            result[f"{stage}_constructed_{metric}"] = clean_number(
                integer(row.get(f"{stage}_constructed_{metric}")), integral=True)
        selected_gates = number(result[f"{stage}_constructed_selected_gates"])
        selected_structures = number(result[f"{stage}_constructed_selected"])
        result[f"{stage}_constructed_gates_per_selected"] = clean_number(
            selected_gates / selected_structures
            if selected_gates is not None and selected_structures else None)

    for field in TIME_FIELDS:
        result[field] = clean_number(number(row.get(field)))

    return result


def numeric_values(rows: Iterable[Dict[str, Any]], field: str) -> List[float]:
    return [parsed for row in rows if (parsed := number(row.get(field))) is not None]


def make_overall(cases: List[Dict[str, Any]]) -> Dict[str, Any]:
    overall: Dict[str, Any] = {field: "" for field in CSV_FIELDS}
    valid = [row for row in cases if row["status"] == "PASS"]
    overall.update({
        "row_type": "overall", "case": "OVERALL", "status": "PASS" if valid else "NO_VALID_CASES",
        "valid_cases": len(valid), "invalid_cases": len(cases) - len(valid),
    })
    for stage in STAGES:
        sources = {row[f"{stage}_gain_attribution"] for row in valid}
        overall[f"{stage}_gain_attribution"] = (
            next(iter(sources)) if len(sources) == 1 else "mixed"
        ) if sources else ""
    sum_fields = [
        "input_and", "after_comb_and", "after_seq_and", "comb_reduced_and",
        "seq_reduced_and", "total_reduced_and", "input_reg", "after_comb_reg",
        "after_seq_reg", "comb_reduced_reg", "seq_reduced_reg", "total_reduced_reg",
        *[field for field in STAGE_FIELDS if not field.endswith("_pct")],
        *[field for field in KIND_FIELDS if not field.endswith("_pct")],
        *[field for field in BUILD_ONLY_FIELDS if not field.endswith("_pct")],
        *[field for field in CONSTRUCT_FIELDS
          if not field.endswith(("_max_gates", "_per_selected"))],
        *[field for field in TIME_FIELDS if field.endswith("_sec")],
        *[field for field in HISTORY_FIELDS if field not in {
            "root_helper_retained_max", "root_helper_endpoints_max",
            "root_batch_relations_max", "root_srm_nodes_max",
        }],
    ]
    for field in sum_fields:
        vals = numeric_values(valid, field)
        if vals:
            value = sum(vals)
            integral = field not in TIME_FIELDS and not field.endswith(
                ("_and_gain", "_reg_gain"))
            overall[field] = clean_number(value, integral=integral)
    for field in [field for field in CONSTRUCT_FIELDS if field.endswith("_max_gates")]:
        vals = numeric_values(valid, field)
        if vals:
            overall[field] = int(max(vals))
    for field in (
        "root_helper_retained_max", "root_helper_endpoints_max",
        "root_batch_relations_max", "root_srm_nodes_max",
    ):
        vals = numeric_values(valid, field)
        if vals:
            overall[field] = int(max(vals))
    profile_total = number(overall["profile_total_sec"])
    for metric in (
        "build_discovery", "seq_proof_shared", "selection", "stage_eval",
        "contribution_eval", "commit", "decision", "overhead", "unprofiled",
    ):
        overall[f"profile_{metric}_pct"] = clean_number(ratio_pct(
            overall[f"profile_{metric}_sec"], profile_total))
    overall["seq_build_path_upper_bound_pct"] = clean_number(ratio_pct(
        overall["seq_build_path_upper_bound_sec"], profile_total))
    upper = number(overall["seq_build_path_upper_bound_sec"])
    ordered_gain = number(overall["seq_constructed_and_gain"])
    if upper and ordered_gain is not None:
        overall["seq_build_ordered_gain_per_upper_bound_sec"] = clean_number(
            ordered_gain / upper)

    overall["comb_reduction_pct"] = clean_number(ratio_pct(
        overall["comb_reduced_and"], overall["input_and"]))
    overall["seq_reduction_pct"] = clean_number(ratio_pct(
        overall["seq_reduced_and"], overall["input_and"]))
    overall["total_reduction_pct"] = clean_number(ratio_pct(
        overall["total_reduced_and"], overall["input_and"]))
    for stage in STAGES:
        overall[f"{stage}_selected_per_proved_pct"] = clean_number(ratio_pct(
            overall[f"{stage}_selected"], overall[f"{stage}_proved"]))
        selected_gates = number(overall[f"{stage}_constructed_selected_gates"])
        selected_structures = number(overall[f"{stage}_constructed_selected"])
        if selected_gates is not None and selected_structures:
            overall[f"{stage}_constructed_gates_per_selected"] = round(
                selected_gates / selected_structures, 6)
        stage_gain = overall[f"{stage}_reduced_and"]
        for kind in KINDS:
            gain_share_pct = ratio_pct(
                overall[f"{stage}_{kind}_and_gain"], stage_gain)
            overall[f"{stage}_{kind}_gain_share_pct"] = clean_number(gain_share_pct)
            reduction_pct = multiplied_pct(
                overall[f"{stage}_reduction_pct"], gain_share_pct)
            if reduction_pct is None:
                reduction_pct = ratio_pct(
                    overall[f"{stage}_{kind}_and_gain"], overall["input_and"])
            overall[f"{stage}_{kind}_reduction_pct"] = clean_number(reduction_pct)
        overall[f"{stage}_build_only_reduction_pct"] = clean_number(ratio_pct(
            overall[f"{stage}_build_only_and_gain"], overall["input_and"]))

    comb_pcts = numeric_values(valid, "comb_reduction_pct")
    seq_pcts = numeric_values(valid, "seq_reduction_pct")
    overall["cases_comb_improved"] = sum(
        (number(row.get("comb_reduced_and")) or 0) > 0 for row in valid)
    overall["cases_seq_improved"] = sum(
        (number(row.get("seq_reduced_and")) or 0) > 0 for row in valid)
    if comb_pcts:
        overall["mean_case_comb_reduction_pct"] = round(statistics.fmean(comb_pcts), 6)
        overall["median_case_comb_reduction_pct"] = round(statistics.median(comb_pcts), 6)
    if seq_pcts:
        overall["mean_case_seq_reduction_pct"] = round(statistics.fmean(seq_pcts), 6)
        overall["median_case_seq_reduction_pct"] = round(statistics.median(seq_pcts), 6)
    return overall


def render_stage(row: Dict[str, Any], stage: str) -> str:
    parts = []
    for kind, label in (("constant", "C"), ("existing", "E"),
                        ("constructed", "B")):
        g = row.get(f'{stage}_{kind}_and_gain', '')
        reduction = row.get(f'{stage}_{kind}_reduction_pct', '')
        g_str = (
            f"g={g} reduction={reduction}%"
            if g != '' and reduction != '' else f"g={g}" if g != '' else ""
        )
        if kind == "constructed":
            build_only_gain = row.get(f"{stage}_build_only_and_gain", "")
            build_only_pct = row.get(f"{stage}_build_only_reduction_pct", "")
            if build_only_gain != "":
                g_str += f" build-only={build_only_gain}({build_only_pct}%)"
        parts.append(
            f"{label}:sel/new={row.get(f'{stage}_{kind}_selected', '')}/"
            f"{row.get(f'{stage}_{kind}_proved', '')} {g_str}"
        )
    return " | ".join(parts)


def print_report(cases: List[Dict[str, Any]], overall: Dict[str, Any]) -> None:
    sorted_cases = sorted(
        cases,
        key=lambda r: number(r.get("total_reduction_pct")) or 0.0,
        reverse=True,
    )
    top = sorted_cases[:100]

    CW = 24   # Case
    IW = 7    # Input
    DW = 7    # Stage Δ
    PW = 10   # Input-normalized Stage % / Total%

    header = (
        f"{'Case':<{CW}} {'Input':>{IW}}  "
        f"{'CombΔ':>{DW}} {'Comb/Input%':>{PW}}  "
        f"{'SeqΔ':>{DW}} {'Seq/Input%':>{PW}}  "
        f"{'Total%':>{PW}}"
    )
    sep = "─" * len(header)

    print(sep)
    print(header)
    print(sep)
    for row in top:
        name = Path(row['case']).name
        comb_pct = row.get("comb_reduction_pct", "")
        seq_pct = row.get("seq_reduction_pct", "")
        total_pct = row.get("total_reduction_pct", "")
        c = f"{comb_pct}%" if comb_pct != "" else ""
        s = f"{seq_pct}%" if seq_pct != "" else ""
        t = f"{total_pct}%" if total_pct != "" else ""
        print(
            f"{name:<{CW}} {str(row['input_and']):>{IW}}  "
            f"{str(row['comb_reduced_and']):>{DW}} {c:>{PW}}  "
            f"{str(row['seq_reduced_and']):>{DW}} {s:>{PW}}  "
            f"{t:>{PW}}"
        )
        if row["status"] == "PASS":
            print(f"  comb {render_stage(row, 'comb')}")
            print(f"  seq  {render_stage(row, 'seq')}")
    print(sep)
    print(
        f"OVERALL: valid={overall['valid_cases']} invalid={overall['invalid_cases']} "
        f"AND {overall['input_and']} -> {overall['after_comb_and']} "
        f"(-{overall['comb_reduced_and']}, {overall['comb_reduction_pct']}%) -> "
        f"{overall['after_seq_and']} "
        f"(-{overall['seq_reduced_and']}, {overall['seq_reduction_pct']}% of input)"
    )
    print(f"  comb {render_stage(overall, 'comb')}")
    print(f"  seq  {render_stage(overall, 'seq')}")
    print(
        "  history/helper "
        f"new-proved={overall['root_new_proved']} "
        f"history-selected={overall['root_history_proved_selected']} | "
        f"retained-max={overall['root_helper_retained_max']} "
        f"injected-events={overall['root_helper_injected_events']} "
        f"inactive-events={overall['root_helper_inactive_events']}"
    )
    print(
        "  note selected/new-proved may exceed 100% when a remapped formal "
        "certificate is selected in a later phase"
    )
    print(
        "  time "+
        f"Build-search={overall['profile_build_discovery_sec']}s "
        f"({overall['profile_build_discovery_pct']}%) | "
        f"shared-seq-proof={overall['profile_seq_proof_shared_sec']}s "
        f"({overall['profile_seq_proof_shared_pct']}%) | "
        f"profiling-overhead={overall['profile_overhead_sec']}s "
        f"({overall['profile_overhead_pct']}%)"
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Analyze &stran combination/sequential stage profiling CSV")
    parser.add_argument("csv", type=Path, help="bench_scorr_then_stran.py output")
    parser.add_argument("--out", type=Path, default=None,
                        help="write CSV to this path (no file written if omitted)")
    parser.add_argument("--quiet", action="store_true",
                        help="suppress the per-case report")
    args = parser.parse_args()

    with args.csv.open("r", newline="", encoding="utf-8") as handle:
        source_rows = list(csv.DictReader(handle))
    if not source_rows:
        sys.exit(f"[ERROR] empty CSV: {args.csv}")
    required = {f"{stage}_{kind}_proved" for stage in STAGES for kind in KINDS}
    missing = sorted(required - set(source_rows[0]))
    if missing:
        sys.exit(
            "[ERROR] CSV has no stage-kind profiling columns; rebuild ABC and "
            "rerun bench_scorr_then_stran.py with &stran -p. Missing: " +
            ", ".join(missing)
        )
    if not any(
        number(row.get(field)) is not None
        for row in source_rows for field in required
    ):
        sys.exit(
            "[ERROR] stage-kind columns contain no profiling data; rebuild ABC "
            "and rerun bench_scorr_then_stran.py with &stran -p"
        )

    cases = [make_case(row) for row in source_rows]
    overall = make_overall(cases)

    if args.out:
        output = args.out
        output.parent.mkdir(parents=True, exist_ok=True)
        temporary = output.with_name(output.name + ".tmp")
        with temporary.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
            writer.writeheader()
            writer.writerows(cases + [overall])
        temporary.replace(output)
        print(f"[INFO] analysis CSV: {output}")

    if not args.quiet:
        print_report(cases, overall)


if __name__ == "__main__":
    main()
