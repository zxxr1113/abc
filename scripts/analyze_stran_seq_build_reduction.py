#!/usr/bin/env python3
"""Rank &stran cases by input-normalized sequential Build reduction.

The raw profiler calls this candidate kind ``constructed``.  This report uses
the presentation name ``Build`` and ranks by::

    Seq Build ordered gain = G(C + E + B) - G(C + E)
    Seq Build reduction (%) = Seq Build ordered gain / input ANDs * 100

Every component reduction percentage written by this script is relative to the
original input AND count, not merely a within-stage share.  Build-only gain is
the separate G(B) counterfactual from the same frozen proved-candidate pool.
Build-search time is exact; sequential-proof time is labelled shared because
direct and Build candidates are proved in the same closure.  Their sum is only
an upper bound on the Build path, not a causal time attribution.
"""

from __future__ import annotations

import argparse
import csv
import math
import os
import sys
from pathlib import Path
from typing import Any

from analyze_stran_stage_profile import KINDS, STAGES, make_case, number


OUTPUT_FIELDS = [
    "rank", "case", "seq_gain_attribution", "input_and",
    "comb_reduced_and", "comb_reduction_pct",
    "comb_constant_reduction_pct", "comb_existing_reduction_pct",
    "comb_build_reduction_pct",
    "seq_reduced_and", "seq_reduction_pct",
    "seq_constant_reduction_pct", "seq_existing_reduction_pct",
    "seq_build_reduction_pct",
    "seq_build_and_gain", "seq_build_gain_share_pct",
    "seq_build_only_reduction_pct", "seq_build_only_and_gain",
    "seq_build_selected", "seq_build_proved",
    "profile_total_sec", "build_discovery_sec", "build_discovery_pct",
    "seq_proof_shared_sec", "seq_proof_shared_pct",
    "decision_sec", "decision_pct",
    "profiling_overhead_sec", "profiling_overhead_pct",
    "seq_build_path_upper_bound_sec", "seq_build_path_upper_bound_pct",
    "seq_build_and_gain_per_upper_bound_sec",
]


def load_source_rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        fields = set(reader.fieldnames or ())
        required = {f"{stage}_{kind}_proved" for stage in STAGES for kind in KINDS}
        missing = sorted(required - fields)
        if missing:
            sys.exit(
                "[ERROR] CSV has no stage-kind profiling columns; rebuild ABC "
                "and rerun bench_scorr_then_stran.py with &stran -p. Missing: "
                + ", ".join(missing)
            )
        rows = list(reader)
    if not rows:
        sys.exit(f"[ERROR] empty CSV: {path}")
    if not any(
        number(row.get(field)) is not None
        for row in rows for field in required
    ):
        sys.exit(
            "[ERROR] stage-kind columns contain no profiling data; rebuild ABC "
            "and rerun bench_scorr_then_stran.py with &stran -p"
        )
    return rows


def ranked_row(source: dict[str, str]) -> tuple[dict[str, Any] | None, str]:
    profile = make_case(source)
    if profile["status"] != "PASS":
        return None, "invalid_status"

    seq_build_reduction = number(profile["seq_constructed_reduction_pct"])
    if seq_build_reduction is None:
        return None, "missing_seq_build_reduction"

    input_and = number(profile["input_and"])
    seq_build_gain = number(profile["seq_constructed_and_gain"])
    if input_and is None or input_and == 0 or seq_build_gain is None:
        return None, "missing_seq_build_input_or_gain"

    # Check the multiplied result against its equivalent direct normalization.
    direct_reduction = 100.0 * seq_build_gain / input_and
    if not math.isclose(seq_build_reduction, direct_reduction, abs_tol=1e-5):
        raise ValueError(
            f"Seq Build percentage mismatch for {profile['case']}: "
            f"multiplied={seq_build_reduction}, direct={direct_reduction}"
        )

    return {
        "rank": 0,
        "case": profile["case"],
        "seq_gain_attribution": profile["seq_gain_attribution"],
        "input_and": profile["input_and"],
        "comb_reduced_and": profile["comb_reduced_and"],
        "comb_reduction_pct": profile["comb_reduction_pct"],
        "comb_constant_reduction_pct": profile["comb_constant_reduction_pct"],
        "comb_existing_reduction_pct": profile["comb_existing_reduction_pct"],
        "comb_build_reduction_pct": profile["comb_constructed_reduction_pct"],
        "seq_reduced_and": profile["seq_reduced_and"],
        "seq_reduction_pct": profile["seq_reduction_pct"],
        "seq_constant_reduction_pct": profile["seq_constant_reduction_pct"],
        "seq_existing_reduction_pct": profile["seq_existing_reduction_pct"],
        "seq_build_reduction_pct": seq_build_reduction,
        "seq_build_and_gain": profile["seq_constructed_and_gain"],
        "seq_build_gain_share_pct": profile["seq_constructed_gain_share_pct"],
        "seq_build_only_reduction_pct": profile["seq_build_only_reduction_pct"],
        "seq_build_only_and_gain": profile["seq_build_only_and_gain"],
        "seq_build_selected": profile["seq_constructed_selected"],
        "seq_build_proved": profile["seq_constructed_proved"],
        "profile_total_sec": profile["profile_total_sec"],
        "build_discovery_sec": profile["profile_build_discovery_sec"],
        "build_discovery_pct": profile["profile_build_discovery_pct"],
        "seq_proof_shared_sec": profile["profile_seq_proof_shared_sec"],
        "seq_proof_shared_pct": profile["profile_seq_proof_shared_pct"],
        "decision_sec": profile["profile_decision_sec"],
        "decision_pct": profile["profile_decision_pct"],
        "profiling_overhead_sec": profile["profile_overhead_sec"],
        "profiling_overhead_pct": profile["profile_overhead_pct"],
        "seq_build_path_upper_bound_sec": profile["seq_build_path_upper_bound_sec"],
        "seq_build_path_upper_bound_pct": profile["seq_build_path_upper_bound_pct"],
        "seq_build_and_gain_per_upper_bound_sec":
            profile["seq_build_ordered_gain_per_upper_bound_sec"],
    }, "included"


def csv_value(field: str, value: Any) -> str:
    if field in {"rank", "case", "seq_gain_attribution"}:
        return str(value)
    if value == "" or value is None:
        return ""
    if field in {
        "input_and", "comb_reduced_and", "seq_reduced_and",
        "seq_build_selected", "seq_build_proved",
    }:
        return str(int(float(value)))
    return f"{float(value):.6f}"


def display_number(value: Any, digits: int) -> str:
    parsed = number(value)
    return f"{parsed:.{digits}f}" if parsed is not None else "N/A"


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
    lines = [
        "| Rank | Case | Seq total / input | Seq Constant / input | "
        "Seq Existing / input | Seq Build / input | Build-only / input | "
        "Build AND | Build-only AND | Selected / Proved | Build search | "
        "Shared seq proof | Profile overhead |",
        "|---:|:---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for row in selected:
        case = str(row["case"]).replace("|", "\\|")
        lines.append(
            f"| {row['rank']} | {case} | {row['seq_reduction_pct']:.6f}% | "
            f"{display_number(row['seq_constant_reduction_pct'], 6)}% | "
            f"{display_number(row['seq_existing_reduction_pct'], 6)}% | "
            f"**{display_number(row['seq_build_reduction_pct'], 6)}%** | "
            f"{display_number(row['seq_build_only_reduction_pct'], 6)}% | "
            f"{display_number(row['seq_build_and_gain'], 3)} | "
            f"{display_number(row['seq_build_only_and_gain'], 3)} | "
            f"{row['seq_build_selected']} / {row['seq_build_proved']} | "
            f"{display_number(row['build_discovery_sec'], 4)}s "
            f"({display_number(row['build_discovery_pct'], 2)}%) | "
            f"{display_number(row['seq_proof_shared_sec'], 4)}s "
            f"({display_number(row['seq_proof_shared_pct'], 2)}%) | "
            f"{display_number(row['profiling_overhead_sec'], 4)}s "
            f"({display_number(row['profiling_overhead_pct'], 2)}%) |"
        )
    return "\n".join(lines) + "\n"


def clip_middle(text: str, width: int) -> str:
    if len(text) <= width:
        return text
    tail = min(16, max(9, width // 3))
    head = width - tail - 1
    return text[:head] + "…" + text[-tail:]


def terminal_table(rows: list[dict[str, Any]], limit: int, case_width: int) -> str:
    selected = rows if limit == 0 else rows[:limit]
    header = (
        f"{'Rank':>4}  {'Case':<{case_width}} | {'Seq/Input':>9} | "
        f"{'Constant':>9} {'Existing':>9} {'Build':>9} {'B-only':>9} | "
        f"{'Build AND':>9} {'B-only AND':>10} {'Sel/Prv':>9} | "
        f"{'B-search%':>9} {'Seq-prf%':>9} {'Prof-ov%':>9}"
    )
    separator = "-" * len(header)
    lines = [header, separator]
    for row in selected:
        case = clip_middle(Path(str(row["case"])).name, case_width)
        selected_proved = f"{row['seq_build_selected']}/{row['seq_build_proved']}"
        build_only_pct = display_number(row["seq_build_only_reduction_pct"], 4)
        build_only_gain = display_number(row["seq_build_only_and_gain"], 3)
        lines.append(
            f"{row['rank']:>4}  {case:<{case_width}} | "
            f"{row['seq_reduction_pct']:>8.4f}% | "
            f"{row['seq_constant_reduction_pct']:>8.4f}% "
            f"{row['seq_existing_reduction_pct']:>8.4f}% "
            f"{row['seq_build_reduction_pct']:>8.4f}% "
            f"{build_only_pct:>8}% | "
            f"{row['seq_build_and_gain']:>9.3f} "
            f"{build_only_gain:>10} {selected_proved:>9} | "
            f"{display_number(row['build_discovery_pct'], 3):>9} "
            f"{display_number(row['seq_proof_shared_pct'], 3):>9} "
            f"{display_number(row['profiling_overhead_pct'], 3):>9}"
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Rank cases by Seq Build reduction as a percentage of input ANDs."
    )
    parser.add_argument("csv", type=Path, help="bench_scorr_then_stran.py output")
    parser.add_argument(
        "--out", type=Path, default=None,
        help="default: <input-stem>_seq_build_ranked.csv",
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
        "--case-width", type=int, default=36,
        help="case-name column width in terminal output (minimum 24)",
    )
    args = parser.parse_args()
    if args.top < 0:
        sys.exit("[ERROR] --top must be nonnegative")
    if args.case_width < 24:
        sys.exit("[ERROR] --case-width must be at least 24")

    input_path = args.csv.expanduser().resolve()
    output_path = (
        args.out.expanduser().resolve()
        if args.out is not None
        else input_path.with_name(input_path.stem + "_seq_build_ranked.csv")
    )
    markdown_path = (
        args.markdown_out.expanduser().resolve()
        if args.markdown_out is not None
        else output_path.with_suffix(".md")
    )

    source_rows = load_source_rows(input_path)
    rows: list[dict[str, Any]] = []
    excluded: dict[str, int] = {}
    for source in source_rows:
        row, reason = ranked_row(source)
        if row is None:
            excluded[reason] = excluded.get(reason, 0) + 1
        else:
            rows.append(row)
    if not rows:
        sys.exit("[ERROR] no valid cases have a Seq Build reduction value")

    rows.sort(key=lambda row: str(row["case"]))
    rows.sort(key=lambda row: row["seq_build_reduction_pct"], reverse=True)
    for rank, row in enumerate(rows, start=1):
        row["rank"] = rank

    write_csv_atomic(output_path, rows)
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(markdown_table(rows, args.top), encoding="utf-8")

    excluded_text = ", ".join(
        f"{reason}={count}" for reason, count in sorted(excluded.items())
    ) or "none"
    shown = len(rows) if args.top == 0 else min(args.top, len(rows))
    print("\nSeq Build reduction ranking")
    print("=" * 52)
    attribution_counts: dict[str, int] = {}
    for row in rows:
        source = str(row["seq_gain_attribution"])
        attribution_counts[source] = attribution_counts.get(source, 0) + 1
    attribution_text = ", ".join(
        f"{source}={count}" for source, count in sorted(attribution_counts.items())
    )
    print(
        "Ordered formula: Seq Build gain = G(C+E+B) - G(C+E); "
        "Build-only = G(B)"
    )
    print(f"Attribution source: {attribution_text}")
    print(
        f"Cases: {len(rows)}/{len(source_rows)} included  |  "
        f"Excluded: {len(source_rows) - len(rows)} ({excluded_text})"
    )
    print("Sorted by: Seq Build reduction (% of original input), descending")
    print(f"\nTop {shown} cases\n")
    print(terminal_table(rows, args.top, args.case_width), end="")
    print(f"\nFull CSV : {output_path}")
    print(f"Markdown : {markdown_path}")


if __name__ == "__main__":
    main()
