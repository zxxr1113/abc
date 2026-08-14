#!/usr/bin/env python3
"""Compare three reductions/times and rank &stran's added contribution.

For every case with usable outputs from all three methods:

    contribution = scorr_then_stran_reduction_pct - scorr_reduction_pct

The contribution is therefore reported in percentage points.  dsec status is
intentionally ignored; this script only analyzes optimization effect and time.
When v2 profile fields are present, the output also carries exact sequential
Build gain, exact Build-search time, shared sequential-proof time, decision
time, and profile-only counterfactual-analysis overhead.
"""

from __future__ import annotations

import argparse
import csv
import math
import os
import statistics
import sys
from pathlib import Path
from typing import Any


OUTPUT_FIELDS = [
    "rank",
    "case",
    "scorr_reduction_pct",
    "scorr_time_s",
    "stran_reduction_pct",
    "stran_time_s",
    "scorr_then_stran_reduction_pct",
    "scorr_then_stran_time_s",
    "contribution_pct_points",
    "stran_seq_build_ordered_and_gain", "stran_seq_build_only_and_gain",
    "stran_seq_build_share_of_reduction_pct",
    "stran_profile_total_s",
    "stran_build_discovery_s", "stran_build_discovery_pct",
    "stran_seq_proof_shared_s", "stran_seq_proof_shared_pct",
    "stran_decision_s", "stran_decision_pct",
    "stran_profile_overhead_s", "stran_profile_overhead_pct",
    "stran_seq_build_path_upper_bound_s",
    "scorr_then_stran_seq_build_ordered_and_gain",
    "scorr_then_stran_seq_build_only_and_gain",
    "scorr_then_stran_seq_build_share_of_extra_reduction_pct",
    "scorr_then_stran_profile_total_s",
    "scorr_then_stran_build_discovery_s",
    "scorr_then_stran_build_discovery_pct",
    "scorr_then_stran_seq_proof_shared_s",
    "scorr_then_stran_seq_proof_shared_pct",
    "scorr_then_stran_decision_s", "scorr_then_stran_decision_pct",
    "scorr_then_stran_profile_overhead_s",
    "scorr_then_stran_profile_overhead_pct",
    "scorr_then_stran_seq_build_path_upper_bound_s",
]

REQUIRED_FIELDS = {
    "file",
    "scorr_status",
    "scorr_and_reduction_pct",
    "scorr_time_ms",
    "stran_status",
    "stran_and_reduction_pct",
    "stran_time_ms",
    "scorr_then_stran_status",
    "scorr_then_stran_and_reduction_pct",
    "scorr_then_stran_time_ms",
}


def number(value: Any) -> float | None:
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def load_rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        missing = REQUIRED_FIELDS - set(reader.fieldnames or ())
        if missing:
            sys.exit("[ERROR] missing CSV fields: " + ", ".join(sorted(missing)))
        return list(reader)


def analyze_row(source: dict[str, str]) -> tuple[dict[str, Any] | None, str]:
    for method in ("scorr", "stran", "scorr_then_stran"):
        if source[f"{method}_status"] != "PASS":
            return None, f"{method}_not_pass"

    scorr_reduction = number(source["scorr_and_reduction_pct"])
    scorr_time_ms = number(source["scorr_time_ms"])
    stran_reduction = number(source["stran_and_reduction_pct"])
    stran_time_ms = number(source["stran_time_ms"])
    combo_reduction = number(source["scorr_then_stran_and_reduction_pct"])
    combo_time_ms = number(source["scorr_then_stran_time_ms"])
    values = (
        scorr_reduction, scorr_time_ms, stran_reduction, stran_time_ms,
        combo_reduction, combo_time_ms,
    )
    if any(value is None for value in values):
        return None, "missing_numeric_field"

    assert scorr_reduction is not None
    assert scorr_time_ms is not None
    assert stran_reduction is not None
    assert stran_time_ms is not None
    assert combo_reduction is not None
    assert combo_time_ms is not None

    result = {
        "rank": 0,
        "case": Path(source["file"]).name,
        "scorr_reduction_pct": scorr_reduction,
        "scorr_time_s": scorr_time_ms / 1000.0,
        "stran_reduction_pct": stran_reduction,
        "stran_time_s": stran_time_ms / 1000.0,
        "scorr_then_stran_reduction_pct": combo_reduction,
        "scorr_then_stran_time_s": combo_time_ms / 1000.0,
        "contribution_pct_points": combo_reduction - scorr_reduction,
    }
    for prefix, output_prefix, reduction_field in (
        ("stran", "stran", "stran_and_reduction"),
        ("scorr_then_stran", "scorr_then_stran",
         "scorr_then_stran_extra_and_reduction"),
    ):
        ordered = number(source.get(f"{prefix}_seq_build_ordered_and_gain"))
        reduction = number(source.get(reduction_field))
        result[f"{output_prefix}_seq_build_ordered_and_gain"] = ordered
        result[f"{output_prefix}_seq_build_only_and_gain"] = number(
            source.get(f"{prefix}_seq_build_only_and_gain"))
        share_name = (
            f"{output_prefix}_seq_build_share_of_extra_reduction_pct"
            if prefix == "scorr_then_stran"
            else f"{output_prefix}_seq_build_share_of_reduction_pct"
        )
        result[share_name] = (
            100.0 * ordered / reduction
            if ordered is not None and reduction not in (None, 0) else None
        )
        for source_suffix, output_suffix in (
            ("profile_total_sec", "profile_total_s"),
            ("profile_build_discovery_sec", "build_discovery_s"),
            ("profile_build_discovery_pct", "build_discovery_pct"),
            ("profile_seq_proof_shared_sec", "seq_proof_shared_s"),
            ("profile_seq_proof_shared_pct", "seq_proof_shared_pct"),
            ("profile_decision_sec", "decision_s"),
            ("profile_decision_pct", "decision_pct"),
            ("profile_overhead_sec", "profile_overhead_s"),
            ("profile_overhead_pct", "profile_overhead_pct"),
            ("seq_build_path_upper_bound_sec", "seq_build_path_upper_bound_s"),
        ):
            result[f"{output_prefix}_{output_suffix}"] = number(
                source.get(f"{prefix}_{source_suffix}"))
    return result, "included"


def print_internal_summary(rows: list[dict[str, Any]], prefix: str, label: str) -> None:
    gains = [
        value for row in rows
        if (value := number(row.get(f"{prefix}_seq_build_ordered_and_gain")))
        is not None
    ]
    totals = [number(row.get(f"{prefix}_profile_total_s")) for row in rows]
    build = [number(row.get(f"{prefix}_build_discovery_s")) for row in rows]
    shared = [number(row.get(f"{prefix}_seq_proof_shared_s")) for row in rows]
    decision = [number(row.get(f"{prefix}_decision_s")) for row in rows]
    overhead = [number(row.get(f"{prefix}_profile_overhead_s")) for row in rows]
    complete = [
        values for values in zip(totals, build, shared, decision, overhead)
        if all(value is not None for value in values)
    ]
    if not gains and not complete:
        print(f"  {label:18s}: no v2 internal profile data")
        return
    gain_text = (
        f"Build ordered gain sum={sum(gains):.0f}, positive-cases="
        f"{sum(value > 0 for value in gains)}/{len(gains)}"
        if gains else "Build gain unavailable"
    )
    if complete:
        total_s = sum(values[0] for values in complete)
        weighted = [
            100.0 * sum(values[index] for values in complete) / total_s
            if total_s else 0.0 for index in range(1, 5)
        ]
        share_values = [
            number(row.get(f"{prefix}_seq_build_share_of_"
                           f"{'extra_reduction' if prefix == 'scorr_then_stran' else 'reduction'}_pct"))
            for row in rows
        ]
        share_values = [value for value in share_values if value is not None]
        share_text = (
            f", median Build/reduction={statistics.median(share_values):.2f}%"
            if share_values else ""
        )
        time_text = (
            f"; weighted time: Build-search={weighted[0]:.2f}%, "
            f"shared-seq-proof={weighted[1]:.2f}%, decision={weighted[2]:.2f}%, "
            f"profile-only={weighted[3]:.2f}%"
        )
    else:
        share_text = time_text = ""
    print(f"  {label:18s}: {gain_text}{share_text}{time_text}")


def csv_value(field: str, value: Any) -> str:
    if field == "rank":
        return str(value)
    if field == "case":
        return str(value)
    return "" if value is None else f"{float(value):.6f}"


def write_csv_atomic(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=OUTPUT_FIELDS)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: csv_value(field, row[field]) for field in OUTPUT_FIELDS})
    os.replace(temporary, path)


def markdown_table(rows: list[dict[str, Any]], limit: int) -> str:
    selected = rows if limit == 0 else rows[:limit]
    headers = (
        "Rank", "Case", "&scorr red. (%)", "&scorr time (s)",
        "&stran red. (%)", "&stran time (s)",
        "&scorr+&stran red. (%)", "&scorr+&stran time (s)",
        "Contribution (p.p.)",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "|---:|:---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in selected:
        case = str(row["case"]).replace("|", "\\|")
        lines.append(
            f"| {row['rank']} | {case} | "
            f"{row['scorr_reduction_pct']:.4f} | {row['scorr_time_s']:.3f} | "
            f"{row['stran_reduction_pct']:.4f} | {row['stran_time_s']:.3f} | "
            f"{row['scorr_then_stran_reduction_pct']:.4f} | "
            f"{row['scorr_then_stran_time_s']:.3f} | "
            f"{row['contribution_pct_points']:.6f} |"
        )
    return "\n".join(lines) + "\n"


def clip_middle(text: str, width: int) -> str:
    """Fit a case name while preserving both its prefix and suffix."""
    if len(text) <= width:
        return text
    tail = min(14, max(8, width // 3))
    head = width - tail - 1
    return text[:head] + "…" + text[-tail:]


def terminal_table(rows: list[dict[str, Any]], limit: int, case_width: int) -> str:
    selected = rows if limit == 0 else rows[:limit]
    header = (
        f"{'Rank':>4}  {'Case':<{case_width}} | "
        f"{'&scorr':^16} | {'&stran':^16} | "
        f"{'&scorr + &stran':^16} | {'Contribution':^12}"
    )
    subheader = (
        f"{'':4}  {'':<{case_width}} | "
        f"{'Red.(%)':>7} {'Time(s)':>8} | "
        f"{'Red.(%)':>7} {'Time(s)':>8} | "
        f"{'Red.(%)':>7} {'Time(s)':>8} | {'p.p.':>12}"
    )
    separator = "-" * len(header)
    lines = [header, subheader, separator]
    for row in selected:
        case = clip_middle(str(row["case"]), case_width)
        lines.append(
            f"{row['rank']:>4}  {case:<{case_width}} | "
            f"{row['scorr_reduction_pct']:>7.3f} {row['scorr_time_s']:>8.3f} | "
            f"{row['stran_reduction_pct']:>7.3f} {row['stran_time_s']:>8.3f} | "
            f"{row['scorr_then_stran_reduction_pct']:>7.3f} "
            f"{row['scorr_then_stran_time_s']:>8.3f} | "
            f"{row['contribution_pct_points']:>+12.6f}"
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Rank the extra percentage-point reduction from &stran after &scorr."
    )
    parser.add_argument("csv", type=Path)
    parser.add_argument(
        "--out", type=Path,
        default=Path("results/scorr_stran_three_way/stran_contribution_ranked.csv"),
        help="full ranked CSV output",
    )
    parser.add_argument(
        "--markdown-out", type=Path, default=None,
        help="Markdown table path; defaults next to --out",
    )
    parser.add_argument(
        "--top", type=int, default=30,
        help="rows in the Markdown/terminal table; 0 prints all",
    )
    parser.add_argument(
        "--case-width", type=int, default=42,
        help="case-name column width in terminal output (minimum 24)",
    )
    args = parser.parse_args()
    if args.top < 0:
        sys.exit("[ERROR] --top must be nonnegative")
    if args.case_width < 24:
        sys.exit("[ERROR] --case-width must be at least 24")

    source_rows = load_rows(args.csv.expanduser().resolve())
    ranked: list[dict[str, Any]] = []
    excluded: dict[str, int] = {}
    for source in source_rows:
        row, reason = analyze_row(source)
        if row is None:
            excluded[reason] = excluded.get(reason, 0) + 1
        else:
            ranked.append(row)
    if not ranked:
        sys.exit("[ERROR] no cases have usable outputs from all three methods")

    ranked.sort(key=lambda row: row["case"])
    ranked.sort(key=lambda row: row["contribution_pct_points"], reverse=True)
    for rank, row in enumerate(ranked, start=1):
        row["rank"] = rank

    output_path = args.out.expanduser().resolve()
    markdown_path = (
        args.markdown_out.expanduser().resolve()
        if args.markdown_out is not None
        else output_path.with_suffix(".md")
    )
    write_csv_atomic(output_path, ranked)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown = markdown_table(ranked, args.top)
    markdown_path.write_text(markdown, encoding="utf-8")

    better = sum(row["contribution_pct_points"] > 0 for row in ranked)
    tied = sum(row["contribution_pct_points"] == 0 for row in ranked)
    worse = sum(row["contribution_pct_points"] < 0 for row in ranked)
    duplicate_names = len(ranked) - len({row["case"] for row in ranked})
    excluded_text = ", ".join(
        f"{reason}={count}" for reason, count in sorted(excluded.items())
    ) or "none"
    print("\nThree-way &scorr / &stran contribution analysis")
    print("=" * 49)
    print(
        f"Cases: {len(ranked)}/{len(source_rows)} included  |  "
        f"Excluded: {len(source_rows) - len(ranked)}  |  dsec ignored"
    )
    print(f"Contribution: better {better}  |  tied {tied}  |  worse {worse}")
    print("Sorted by: (&scorr + &stran reduction) - (&scorr reduction), descending")
    print(f"Excluded detail: {excluded_text}")
    print("Internal Seq Build/profile summary (time percentages are weighted)")
    print_internal_summary(ranked, "stran", "&stran")
    print_internal_summary(ranked, "scorr_then_stran", "&scorr -> &stran")
    if duplicate_names:
        print(f"Note: basename-only output contains {duplicate_names} duplicate case names")
    shown = len(ranked) if args.top == 0 else min(args.top, len(ranked))
    print(f"\nTop {shown} cases\n")
    print(terminal_table(ranked, args.top, args.case_width), end="")
    print(f"\nFull CSV : {output_path}")
    print(f"Markdown : {markdown_path}")


if __name__ == "__main__":
    main()
