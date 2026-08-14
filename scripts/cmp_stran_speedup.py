#!/usr/bin/env python3
"""Paired comparison of two &stran CSVs using per-case percentages.

Negative time change means the method is faster.  Negative final-AND change
means the method produces a smaller graph.  Aggregate sums are intentionally
not reported because a few large cases would dominate them.
"""

from __future__ import annotations

import argparse
import csv
import statistics
import sys
from pathlib import Path
from typing import Any, Callable


NA = "N/A"


def load(path: Path) -> dict[str, dict[str, str]]:
    with path.open("r", encoding="utf-8") as handle:
        rows = {
            row.get("file", "").strip(): row
            for row in csv.DictReader(handle)
            if row.get("file", "").strip()
        }
    if not rows:
        sys.exit(f"[ERROR] empty CSV: {path}")
    return rows


def fval(value: Any) -> float | None:
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def ok(row: dict[str, str]) -> bool:
    error = row.get("error", "")
    dsec = row.get("dsec_status", row.get("stran_dsec_status", "SKIP"))
    return (
        row.get("scorr_status") == "PASS"
        and row.get("stran_status") == "PASS"
        and dsec in ("PASS", "SKIP")
        and (not error or error == NA)
    )


def change(method: Any, baseline: Any) -> float | None:
    method_f, baseline_f = fval(method), fval(baseline)
    if method_f is None or baseline_f is None or baseline_f <= 0:
        return None
    return 100.0 * (method_f / baseline_f - 1.0)


def delta(method: Any, baseline: Any) -> float | None:
    method_f, baseline_f = fval(method), fval(baseline)
    if method_f is None or baseline_f is None:
        return None
    return method_f - baseline_f


def rate(value: Any, denominator: Any) -> float | None:
    value_f, denominator_f = fval(value), fval(denominator)
    if value_f is None or denominator_f is None or denominator_f <= 0:
        return None
    return 100.0 * value_f / denominator_f


def first(row: dict[str, str], *fields: str) -> float | None:
    """Read the first numeric field across legacy and three-way schemas."""
    for field in fields:
        value = fval(row.get(field))
        if value is not None:
            return value
    return None


def short(name: str, width: int) -> str:
    if len(name) <= width:
        return name
    base = name.rsplit("/", 1)[-1]
    if len(base) <= width:
        return base
    return "..." + name[-(width - 3):]


def describe(label: str, values: list[float], unit: str = "%") -> None:
    if not values:
        print(f"  {label:>28s}: no data")
        return
    negative = sum(value < 0 for value in values)
    zero = sum(value == 0 for value in values)
    positive = sum(value > 0 for value in values)
    print(
        f"  {label:>28s}: n={len(values):>4} "
        f"mean={statistics.fmean(values):>9.3f}{unit} "
        f"median={statistics.median(values):>9.3f}{unit} "
        f"neg/zero/pos={negative}/{zero}/{positive}"
    )


def metadata_values(rows: dict[str, dict[str, str]], field: str) -> set[str]:
    return {
        row.get(field, "") for row in rows.values()
        if row.get(field, "") not in ("", NA)
    }


def compare_metadata(
    baseline: dict[str, dict[str, str]], method: dict[str, dict[str, str]]
) -> None:
    print("\nRun provenance")
    fields = (
        "run_schema", "git_commit", "git_dirty", "abc_sha256", "scorr_args",
        "stran_args", "stran_args_requested", "stran_args_effective",
    )
    any_metadata = False
    for field in fields:
        base_values = metadata_values(baseline, field)
        method_values = metadata_values(method, field)
        if not base_values and not method_values:
            continue
        any_metadata = True
        base_text = " | ".join(sorted(base_values)) or NA
        method_text = " | ".join(sorted(method_values)) or NA
        if "sha256" in field:
            base_text = base_text[:16]
            method_text = method_text[:16]
        marker = "" if base_values == method_values else "  [DIFF]"
        print(f"  {field:>12s}: baseline={base_text} method={method_text}{marker}")
    if not any_metadata:
        print("  legacy CSVs: provenance unavailable")
        print("  [WARN] same implementation and command-line budgets cannot be established")


def main() -> None:
    parser = argparse.ArgumentParser(description="Paired per-case &stran comparison")
    parser.add_argument("baseline", type=Path)
    parser.add_argument("method", type=Path)
    parser.add_argument(
        "--top", type=int, default=None,
        help="limit displayed pairs only; aggregates still use every valid pair",
    )
    parser.add_argument("--min-baseline-ms", type=int, default=0)
    parser.add_argument("--name-len", type=int, default=50)
    parser.add_argument("--no-per-file", action="store_true")
    parser.add_argument(
        "--sort-by", choices=("time", "quality", "baseline-time"), default="time")
    args = parser.parse_args()

    baseline_rows = load(args.baseline)
    method_rows = load(args.method)
    common = sorted(set(baseline_rows) & set(method_rows))
    paired_names = [
        name for name in common
        if ok(baseline_rows[name]) and ok(method_rows[name])
    ]
    if not paired_names:
        sys.exit("[ERROR] no common valid cases")

    pairs: list[dict[str, Any]] = []
    for name in paired_names:
        baseline = baseline_rows[name]
        method = method_rows[name]
        baseline_ms = first(baseline, "stran_time_ms", "time_ms")
        method_ms = first(method, "stran_time_ms", "time_ms")
        if baseline_ms is None or method_ms is None or baseline_ms <= 0:
            continue
        if baseline_ms < args.min_baseline_ms:
            continue
        baseline_and = fval(baseline.get("stran_and"))
        method_and = fval(method.get("stran_and"))
        baseline_scorr = fval(baseline.get("scorr_and"))
        method_scorr = fval(method.get("scorr_and"))
        baseline_extra_rate = rate(
            baseline.get("stran_extra_and_reduction"), baseline_scorr)
        method_extra_rate = rate(
            method.get("stran_extra_and_reduction"), method_scorr)
        pairs.append({
            "name": name,
            "baseline_ms": baseline_ms,
            "method_ms": method_ms,
            "time_change_pct": change(method_ms, baseline_ms),
            "final_and_change_pct": change(method_and, baseline_and),
            "baseline_and": baseline_and,
            "method_and": method_and,
            "same_scorr_counts": (
                baseline.get("scorr_and") == method.get("scorr_and")
                and baseline.get("scorr_latches") == method.get("scorr_latches")
            ),
            "extra_rate_change_pp": (
                method_extra_rate - baseline_extra_rate
                if method_extra_rate is not None and baseline_extra_rate is not None else None
            ),
            "proof_change_pct": change(method.get("proofs"), baseline.get("proofs")),
            "profile_change_pct": change(
                first(method, "stran_profile_total_sec", "profile_total_sec",
                      "profile_total_ms"),
                first(baseline, "stran_profile_total_sec", "profile_total_sec",
                      "profile_total_ms")),
            "seq_build_ordered_gain_delta": delta(
                first(method, "stran_seq_build_ordered_and_gain",
                      "seq_build_ordered_and_gain"),
                first(baseline, "stran_seq_build_ordered_and_gain",
                      "seq_build_ordered_and_gain")),
            "build_discovery_share_change_pp": (
                (first(method, "stran_profile_build_discovery_pct",
                       "profile_build_discovery_pct") or 0.0) -
                (first(baseline, "stran_profile_build_discovery_pct",
                       "profile_build_discovery_pct") or 0.0)
                if first(method, "stran_profile_build_discovery_pct",
                         "profile_build_discovery_pct") is not None
                and first(baseline, "stran_profile_build_discovery_pct",
                          "profile_build_discovery_pct") is not None else None
            ),
            "seq_proof_share_change_pp": (
                (first(method, "stran_profile_seq_proof_shared_pct",
                       "profile_seq_proof_shared_pct") or 0.0) -
                (first(baseline, "stran_profile_seq_proof_shared_pct",
                       "profile_seq_proof_shared_pct") or 0.0)
                if first(method, "stran_profile_seq_proof_shared_pct",
                         "profile_seq_proof_shared_pct") is not None
                and first(baseline, "stran_profile_seq_proof_shared_pct",
                          "profile_seq_proof_shared_pct") is not None else None
            ),
            "profile_overhead_share_change_pp": (
                (first(method, "stran_profile_overhead_pct",
                       "profile_overhead_pct") or 0.0) -
                (first(baseline, "stran_profile_overhead_pct",
                       "profile_overhead_pct") or 0.0)
                if first(method, "stran_profile_overhead_pct",
                         "profile_overhead_pct") is not None
                and first(baseline, "stran_profile_overhead_pct",
                          "profile_overhead_pct") is not None else None
            ),
        })
    if not pairs:
        sys.exit("[ERROR] no pairs after timing filters")

    sorters: dict[str, Callable[[dict[str, Any]], float]] = {
        "time": lambda pair: abs(pair.get("time_change_pct") or 0),
        "quality": lambda pair: abs(pair.get("final_and_change_pct") or 0),
        "baseline-time": lambda pair: pair["baseline_ms"],
    }
    pairs.sort(key=sorters[args.sort_by], reverse=True)
    display_pairs = pairs[:max(args.top, 0)] if args.top is not None else pairs

    print(
        f"baseline-valid={sum(ok(row) for row in baseline_rows.values())} "
        f"method-valid={sum(ok(row) for row in method_rows.values())} "
        f"common-valid={len(paired_names)} analyzed={len(pairs)}"
    )
    compare_metadata(baseline_rows, method_rows)
    different_scorr = sum(not pair["same_scorr_counts"] for pair in pairs)
    print(
        f"  post-scorr count check: same={len(pairs) - different_scorr} "
        f"different={different_scorr}"
    )
    if different_scorr:
        print("  [WARN] comparisons with different post-scorr counts are confounded")

    if not args.no_per_file:
        print("\nPer-case comparison (negative is better for time and final AND)")
        header = (
            f"{'file':{args.name_len}s} {'base_ms':>10} {'method_ms':>10} "
            f"{'timeΔ%':>10} {'finalANDΔ%':>12} {'extra-rateΔpp':>14}"
        )
        print(header)
        print("-" * len(header))
        for pair in display_pairs:
            quality = pair.get("final_and_change_pct")
            extra = pair.get("extra_rate_change_pp")
            print(
                f"{short(pair['name'], args.name_len):{args.name_len}s} "
                f"{int(pair['baseline_ms']):>10,} {int(pair['method_ms']):>10,} "
                f"{pair['time_change_pct']:>10.2f} "
                f"{(f'{quality:.3f}' if quality is not None else NA):>12s} "
                f"{(f'{extra:.3f}' if extra is not None else NA):>14s}"
            )

    print("\nPaired summary: compute each case first, then average")
    describe("method time change", [pair["time_change_pct"] for pair in pairs])
    describe(
        "final AND change",
        [pair["final_and_change_pct"] for pair in pairs if pair["final_and_change_pct"] is not None],
    )
    describe(
        "extra reduction-rate change",
        [pair["extra_rate_change_pp"] for pair in pairs if pair["extra_rate_change_pp"] is not None],
        unit="pp",
    )
    describe(
        "proof-count change",
        [pair["proof_change_pct"] for pair in pairs if pair["proof_change_pct"] is not None],
    )
    describe(
        "internal-profile change",
        [pair["profile_change_pct"] for pair in pairs if pair["profile_change_pct"] is not None],
    )
    describe(
        "Seq Build ordered-gain delta",
        [pair["seq_build_ordered_gain_delta"] for pair in pairs
         if pair["seq_build_ordered_gain_delta"] is not None],
        unit=" AND",
    )
    for label, field in (
        ("Build-search time-share change", "build_discovery_share_change_pp"),
        ("shared seq-proof share change", "seq_proof_share_change_pp"),
        ("profiling-overhead share change", "profile_overhead_share_change_pp"),
    ):
        describe(label, [pair[field] for pair in pairs if pair[field] is not None],
                 unit="pp")
    quality_pairs = [
        pair for pair in pairs
        if pair.get("baseline_and") is not None and pair.get("method_and") is not None
    ]
    better = sum(pair["method_and"] < pair["baseline_and"] for pair in quality_pairs)
    equal = sum(pair["method_and"] == pair["baseline_and"] for pair in quality_pairs)
    worse = sum(pair["method_and"] > pair["baseline_and"] for pair in quality_pairs)
    print(f"  {'final AND better/equal/worse':>28s}: {better}/{equal}/{worse}")


if __name__ == "__main__":
    main()
