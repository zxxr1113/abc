#!/usr/bin/env python3
"""Plot fair three-way &scorr/&stran reduction and runtime summaries.

Only common cases for which all three pipelines produced usable outputs are
included.  This paired filter prevents independent failure sets from making
one method's aggregate reduction look artificially better.  dsec status is
intentionally not part of this effect/runtime summary.
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from pathlib import Path
from typing import Any

import matplotlib as mpl

mpl.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


mpl.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["Arial", "Helvetica", "DejaVu Sans", "sans-serif"],
    "svg.fonttype": "none",
    "pdf.fonttype": 42,
    "font.size": 7,
    "axes.labelsize": 7.2,
    "axes.titlesize": 8,
    "xtick.labelsize": 7,
    "ytick.labelsize": 6.5,
    "axes.spines.right": False,
    "axes.spines.top": False,
    "axes.linewidth": 0.75,
    "xtick.major.width": 0.7,
    "ytick.major.width": 0.7,
})

METHODS = (
    ("scorr", "&scorr", "#5279A3"),
    ("stran", "&stran", "#D58A45"),
    ("scorr_then_stran", "&scorr → &stran", "#4F9472"),
)
NA = "N/A"


def finite_number(value: Any) -> float | None:
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def required_fields() -> set[str]:
    fields = {"file", "base_and"}
    for key, _, _ in METHODS:
        fields.update({
            f"{key}_status", f"{key}_and",
            f"{key}_and_reduction", f"{key}_and_reduction_pct",
            f"{key}_time_ms",
        })
    return fields


def load_rows(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        missing = required_fields() - set(reader.fieldnames or ())
        if missing:
            sys.exit("[ERROR] missing CSV fields: " + ", ".join(sorted(missing)))
        return list(reader)


def method_valid(row: dict[str, str], method: str) -> bool:
    return (
        row[f"{method}_status"] == "PASS"
        and finite_number(row["base_and"]) is not None
        and finite_number(row[f"{method}_and"]) is not None
        and finite_number(row[f"{method}_and_reduction"]) is not None
        and finite_number(row[f"{method}_and_reduction_pct"]) is not None
        and finite_number(row[f"{method}_time_ms"]) is not None
    )


def percentile(values: list[float], level: float) -> float:
    return float(np.percentile(np.asarray(values, dtype=float), level))


def summarize(
    paired: list[dict[str, str]],
    all_rows: list[dict[str, str]],
) -> list[dict[str, Any]]:
    total_base = sum(finite_number(row["base_and"]) or 0.0 for row in paired)
    if total_base <= 0:
        sys.exit("[ERROR] paired rows have no positive normalized AND total")

    summary: list[dict[str, Any]] = []
    for key, label, color in METHODS:
        reductions = [
            finite_number(row[f"{key}_and_reduction"]) or 0.0 for row in paired
        ]
        percentages = [
            finite_number(row[f"{key}_and_reduction_pct"]) or 0.0 for row in paired
        ]
        times = [
            (finite_number(row[f"{key}_time_ms"]) or 0.0) / 1000.0
            for row in paired
        ]
        total_reduction = sum(reductions)
        summary.append({
            "method": key,
            "label": label,
            "color": color,
            "paired_n": len(paired),
            "independently_valid_n": sum(
                method_valid(row, key) for row in all_rows
            ),
            "total_and_reduction": int(round(total_reduction)),
            "aggregate_and_reduction_pct": 100.0 * total_reduction / total_base,
            "median_and_reduction_pct": percentile(percentages, 50),
            "q1_and_reduction_pct": percentile(percentages, 25),
            "q3_and_reduction_pct": percentile(percentages, 75),
            "median_time_s": percentile(times, 50),
            "q1_time_s": percentile(times, 25),
            "q3_time_s": percentile(times, 75),
        })
    return summary


def comparison_counts(paired: list[dict[str, str]]) -> tuple[int, int, int]:
    better = equal = worse = 0
    for row in paired:
        scorr_and = finite_number(row["scorr_and"])
        combo_and = finite_number(row["scorr_then_stran_and"])
        if scorr_and is None or combo_and is None:
            continue
        if combo_and < scorr_and:
            better += 1
        elif combo_and == scorr_and:
            equal += 1
        else:
            worse += 1
    return better, equal, worse


def write_summary(path: Path, summary: list[dict[str, Any]]) -> None:
    fields = [key for key in summary[0] if key != "color"]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows({key: row[key] for key in fields} for row in summary)


def save_figure(fig: mpl.figure.Figure, stem: Path) -> None:
    fig.savefig(stem.with_suffix(".svg"), bbox_inches="tight")
    fig.savefig(stem.with_suffix(".pdf"), bbox_inches="tight")
    fig.savefig(stem.with_suffix(".png"), dpi=400, bbox_inches="tight")
    fig.savefig(stem.with_suffix(".tiff"), dpi=600, bbox_inches="tight")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Plot paired reduction and runtime for three optimization pipelines."
    )
    parser.add_argument("csv", type=Path)
    parser.add_argument(
        "--out", type=Path,
        default=Path("results/scorr_stran_three_way/three_way_comparison"),
    )
    args = parser.parse_args()

    input_path = args.csv.expanduser().resolve()
    output_stem = args.out.expanduser().resolve()
    output_stem.parent.mkdir(parents=True, exist_ok=True)
    rows = load_rows(input_path)
    paired = [
        row for row in rows
        if all(method_valid(row, key) for key, _, _ in METHODS)
    ]
    if not paired:
        sys.exit("[ERROR] no common eligible cases across the three pipelines")

    summary = summarize(paired, rows)
    better, equal, worse = comparison_counts(paired)
    positions = np.arange(len(METHODS), dtype=float)
    labels = [row["label"] for row in summary]
    colors = [row["color"] for row in summary]

    fig, (ax_reduction, ax_time) = plt.subplots(
        1, 2, figsize=(7.08, 2.75), gridspec_kw={"wspace": 0.34}
    )
    fig.subplots_adjust(left=0.085, right=0.985, top=0.79, bottom=0.25)

    reduction_values = [row["aggregate_and_reduction_pct"] for row in summary]
    bars = ax_reduction.bar(
        positions, reduction_values, width=0.62, color=colors,
        edgecolor="white", linewidth=0.6, zorder=3,
    )
    for bar, value in zip(bars, reduction_values):
        ax_reduction.text(
            bar.get_x() + bar.get_width() / 2, value + 0.45, f"{value:.1f}%",
            ha="center", va="bottom", fontsize=7, fontweight="bold",
        )
    ax_reduction.set_xticks(positions, labels)
    ax_reduction.set_ylabel("Aggregate AND reduction (%)")
    ax_reduction.set_title("Reduction from the same normalized inputs", pad=8)
    ax_reduction.set_ylim(0, 1.18 * max(reduction_values))
    ax_reduction.grid(axis="y", color="#E5E8EB", linewidth=0.6, zorder=0)
    ax_reduction.text(
        0.02, 0.96,
        f"&scorr → &stran vs &scorr: {better} better, {equal} tied, {worse} worse",
        transform=ax_reduction.transAxes, ha="left", va="top", fontsize=6.2,
        color="#394149",
    )

    time_values = [row["median_time_s"] for row in summary]
    bars = ax_time.bar(
        positions, time_values, width=0.62, color=colors,
        edgecolor="white", linewidth=0.6, zorder=3,
    )
    for bar, value in zip(bars, time_values):
        label = f"{value:.2f} s" if value < 10 else f"{value:.1f} s"
        ax_time.text(
            bar.get_x() + bar.get_width() / 2, value + 0.06 * max(time_values),
            label, ha="center", va="bottom", fontsize=7, fontweight="bold",
        )
    ax_time.set_xticks(positions, labels)
    ax_time.set_ylabel("Median wall time per case (s)")
    ax_time.set_title("Optimization runtime", pad=8)
    ax_time.set_ylim(0, 1.25 * max(time_values))
    ax_time.grid(axis="y", color="#E5E8EB", linewidth=0.6, zorder=0)

    for label, axis in zip("ab", (ax_reduction, ax_time)):
        axis.text(
            -0.16, 1.10, label, transform=axis.transAxes,
            fontsize=9, fontweight="bold", va="top",
        )

    fig.suptitle(
        "Three-way reduction and runtime comparison",
        x=0.07, y=0.965, ha="left", fontsize=9.2, fontweight="bold",
    )
    fig.text(
        0.07, 0.035,
        f"n = {len(paired)} common cases with usable outputs from all three methods. "
        "Runtime includes optimization passes only; the combined runtime includes both passes.",
        ha="left", va="bottom", fontsize=6, color="#5E666E",
    )

    save_figure(fig, output_stem)
    plt.close(fig)
    summary_path = output_stem.with_name(output_stem.name + "_summary.csv")
    write_summary(summary_path, summary)

    print(
        f"[INFO] rows={len(rows)} paired={len(paired)} excluded={len(rows) - len(paired)} "
        "dsec=ignored"
    )
    for row in summary:
        print(
            f"[INFO] {row['method']}: independently_valid={row['independently_valid_n']} "
            f"aggregate_reduction={row['aggregate_and_reduction_pct']:.3f}% "
            f"median_reduction={row['median_and_reduction_pct']:.3f}% "
            f"median_time={row['median_time_s']:.3f}s"
        )
    print(
        f"[INFO] paired combo-vs-scorr: better={better} equal={equal} worse={worse}"
    )
    print(f"[INFO] figure stem: {output_stem}")
    print(f"[INFO] summary CSV: {summary_path}")


if __name__ == "__main__":
    main()
