#!/usr/bin/env python3
"""Create a publication-style &stran -B scaling figure from sweep CSV data."""

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
    "axes.labelsize": 7,
    "axes.titlesize": 7.5,
    "xtick.labelsize": 6.5,
    "ytick.labelsize": 6.5,
    "axes.spines.right": False,
    "axes.spines.top": False,
    "axes.linewidth": 0.7,
    "xtick.major.width": 0.7,
    "ytick.major.width": 0.7,
    "legend.frameon": False,
    "legend.fontsize": 6.2,
})

NAVY = "#365F8D"
BLUE = "#73A6C9"
ORANGE = "#D98C4A"
GRAY = "#A8ADB3"
DARK = "#20252B"


def number(value: Any) -> float | None:
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def load_valid(path: Path) -> tuple[list[dict[str, Any]], int, int]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        source = list(csv.DictReader(handle))
    rows: list[dict[str, Any]] = []
    for row in source:
        if row.get("status") != "PASS" or row.get("dsec_status") not in {"PASS", "SKIP"}:
            continue
        required = {
            key: number(row.get(key))
            for key in (
                "b_value", "root_coverage_pct", "and_reduction",
            )
        }
        if any(value is None for value in required.values()):
            continue
        row.update(required)
        rows.append(row)
    rows.sort(key=lambda row: (row["b_value"] == 0, row["b_value"]))
    return rows, len(source), len(source) - len(rows)


def average_ranks(values: np.ndarray) -> np.ndarray:
    order = np.argsort(values, kind="mergesort")
    ranks = np.empty(len(values), dtype=float)
    start = 0
    while start < len(values):
        end = start + 1
        while end < len(values) and values[order[end]] == values[order[start]]:
            end += 1
        ranks[order[start:end]] = 0.5 * (start + end - 1) + 1.0
        start = end
    return ranks


def spearman_rho(x: np.ndarray, y: np.ndarray) -> float:
    x_rank, y_rank = average_ranks(x), average_ranks(y)
    if np.std(x_rank) == 0 or np.std(y_rank) == 0:
        return float("nan")
    return float(np.corrcoef(x_rank, y_rank)[0, 1])


def save_figure(fig: mpl.figure.Figure, output_stem: Path) -> None:
    output_stem.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_stem.with_suffix(".svg"))
    fig.savefig(output_stem.with_suffix(".pdf"))
    fig.savefig(output_stem.with_suffix(".png"), dpi=400)
    fig.savefig(output_stem.with_suffix(".tiff"), dpi=600)


def main() -> None:
    parser = argparse.ArgumentParser(description="Plot candidate-coverage scaling for &stran -B.")
    parser.add_argument("csv", type=Path)
    parser.add_argument("--out", type=Path,
                        default=Path("results/stran_b_scaling/b_scaling"))
    parser.add_argument("--case-label", default="selected sequential case")
    parser.add_argument("--no-text", action="store_true",
                        help="remove titles, axis labels, panel labels, and annotations; keep tick values")
    args = parser.parse_args()

    rows, source_count, excluded_count = load_valid(args.csv.expanduser().resolve())
    if len(rows) < 3:
        sys.exit("[ERROR] need at least three valid, equivalent B-sweep rows")

    b_labels = ["All" if row["b_value"] == 0 else str(int(row["b_value"])) for row in rows]
    positions = np.arange(len(rows), dtype=float)
    coverage = np.array([row["root_coverage_pct"] for row in rows], dtype=float)
    reduction = np.array([row["and_reduction"] for row in rows], dtype=float)
    rho = spearman_rho(coverage, reduction)

    # Collapse repeated coverage values only for drawing the observed trend;
    # every raw B setting remains visible as a point and enters Spearman rho.
    observed_coverage = np.unique(coverage)
    observed_reduction = np.array([
        np.mean(reduction[coverage == value]) for value in observed_coverage
    ])
    if np.any(observed_coverage <= 0) or np.any(observed_reduction <= 0):
        sys.exit("[ERROR] power-law hypothesis requires positive coverage and reduction")
    beta, _ = np.polyfit(
        np.log(observed_coverage), np.log(observed_reduction), 1
    )
    coverage_ceiling = float(observed_coverage[-1])
    reduction_at_ceiling = float(observed_reduction[-1])
    hypothesis_coverage = np.linspace(coverage_ceiling, 100.0, 100)
    hypothesis_reduction = reduction_at_ceiling * (
        hypothesis_coverage / coverage_ceiling
    ) ** beta

    coverage_changes = np.ptp(coverage) > 0
    reduction_changes = np.ptp(reduction) > 0
    if coverage_changes and not reduction_changes:
        conclusion = "Root coverage scales with B, while reduction saturates on this case"
    elif math.isfinite(rho) and rho >= 0.7:
        conclusion = "Higher root coverage tracks higher AND reduction on this case"
    elif math.isfinite(rho) and rho <= -0.7:
        conclusion = "Higher root coverage does not improve reduction on this case"
    else:
        conclusion = "Root coverage and AND reduction are not monotonic on this case"

    fig, axes = plt.subplots(
        1, 3, figsize=(7.08, 2.75),
        gridspec_kw={"width_ratios": [1.0, 1.0, 1.25], "wspace": 0.40},
    )
    fig.subplots_adjust(left=0.075, right=0.985, top=0.77, bottom=0.25)
    ax_a, ax_b, ax_c = axes

    ax_a.plot(positions, coverage, color=NAVY, marker="o", ms=3.8, lw=1.6)
    ax_a.fill_between(positions, coverage, 0, color=NAVY, alpha=0.08)
    ax_a.set_ylabel("Root coverage (%)")
    ax_a.set_xlabel("Candidate-pool size per victim, B")
    ax_a.set_xticks(positions, b_labels)
    ax_a.set_ylim(0, min(100.0, 1.12 * np.max(coverage)))
    ax_a.grid(axis="y", color="#E8EAED", lw=0.55, zorder=0)

    ax_b.plot(positions, reduction, color=ORANGE, marker="o", ms=3.8, lw=1.6)
    ax_b.fill_between(positions, reduction, 0, color=ORANGE, alpha=0.10)
    ax_b.set_ylim(0, 1.12 * np.max(reduction))
    ax_b.set_ylabel("AND reduction")
    ax_b.set_xlabel("Candidate-pool size per victim, B")
    ax_b.set_xticks(positions, b_labels)
    ax_b.grid(axis="y", color="#E8EAED", lw=0.55, zorder=0)

    ax_c.axvspan(coverage_ceiling, 100.0, color=ORANGE, alpha=0.055, lw=0)
    ax_c.plot(observed_coverage, observed_reduction, color=NAVY, lw=1.8,
              marker="o", ms=3.8, zorder=3, label="Observed trend")
    ax_c.scatter(coverage, reduction, s=15, color=NAVY, alpha=0.38,
                 edgecolor="none", zorder=2)
    ax_c.plot(hypothesis_coverage, hypothesis_reduction, color=ORANGE,
              lw=1.8, ls=(0, (4, 2.5)), zorder=3,
              label="Hypothesized continuation")
    ax_c.scatter([hypothesis_coverage[-1]], [hypothesis_reduction[-1]],
                 s=25, facecolor="white", edgecolor=ORANGE, lw=1.2, zorder=4)
    ax_c.axvline(coverage_ceiling, color=GRAY, lw=0.8, ls=":", zorder=1)
    rho_text = f"Spearman ρ = {rho:.2f}" if math.isfinite(rho) else "Spearman ρ = undefined"
    ax_c.text(0.03, 0.96, f"Observed\n{rho_text}\nn = {len(rows)} B settings",
              transform=ax_c.transAxes, ha="left", va="top", fontsize=6.0)
    ax_c.text(0.67, 0.96, "Hypothesis", transform=ax_c.transAxes,
              ha="left", va="top", fontsize=6.2, color=ORANGE,
              fontweight="bold")
    target_x = 88.0
    target_y = reduction_at_ceiling * (target_x / coverage_ceiling) ** beta
    ax_c.annotate(
        "Improve candidate\nquality",
        xy=(target_x, target_y), xytext=(68, target_y + 6.0),
        textcoords="data", ha="center", va="bottom", fontsize=6.0,
        color=ORANGE,
        arrowprops={"arrowstyle": "->", "color": ORANGE, "lw": 0.9},
    )
    ax_c.set_xlabel("Root coverage (%)")
    ax_c.set_ylabel("AND reduction")
    ax_c.set_xlim(15, 102)
    ax_c.set_ylim(0, 1.12 * max(np.max(reduction), hypothesis_reduction[-1]))
    ax_c.grid(color="#E8EAED", lw=0.55, zorder=0)

    for axis in (ax_a, ax_b):
        axis.tick_params(axis="x", labelsize=5.8)

    for label, axis in zip("abc", axes):
        axis.text(-0.20, 1.08, label, transform=axis.transAxes, fontsize=9,
                  fontweight="bold", va="top")

    fig.suptitle(f"&stran scaling: candidate pool → coverage → reduction ({args.case_label})",
                 x=0.055, y=0.965, ha="left", fontsize=9.2, fontweight="bold")
    fig.text(
        0.055, 0.875,
        "Larger candidate pools raise coverage and reduction; better candidates may extend the trend.",
        ha="left", va="top", fontsize=7.2, color=DARK,
    )
    fig.text(
        0.055, 0.025,
        "Single deterministic AIG case; B=All denotes an unlimited pool. "
        "Coverage = roots returning ≥1 constructed candidate / roots searched.\n"
        "Dashed curve = hypothesized power-law continuation beyond observed coverage (not data).",
        ha="left", va="bottom", fontsize=5.8, color="#626970", linespacing=1.15,
    )

    if args.no_text:
        for text_artist in list(fig.texts):
            text_artist.remove()
        for axis in axes:
            for text_artist in list(axis.texts):
                text_artist.remove()
            axis.set_xlabel("")
            axis.set_ylabel("")
        fig.set_size_inches(7.08, 2.40)
        fig.subplots_adjust(left=0.055, right=0.985, top=0.96, bottom=0.13)

    save_figure(fig, args.out.expanduser().resolve())
    plt.close(fig)
    print(
        f"[INFO] rows={source_count} valid={len(rows)} excluded={excluded_count} "
        f"rho={rho:.4f} beta={beta:.4f} "
        f"hypothesis_at_100={hypothesis_reduction[-1]:.3f} "
        f"mode={'no-text' if args.no_text else 'annotated'} conclusion={conclusion}"
    )
    print(f"[INFO] figure stem: {args.out.expanduser().resolve()}")


if __name__ == "__main__":
    main()
