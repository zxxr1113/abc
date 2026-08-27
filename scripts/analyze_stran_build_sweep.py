#!/usr/bin/env python3
"""Analyze phase=SEQ Build gain and discovery cost across paired sweeps."""

from __future__ import annotations

import argparse
import csv
import math
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


NA = {None, "", "N/A"}


def number(value: object) -> float | None:
    if value in NA:
        return None
    try:
        return float(value)  # type: ignore[arg-type]
    except (TypeError, ValueError):
        return None


def ratio(numerator: object, denominator: object) -> float | None:
    num, den = number(numerator), number(denominator)
    if num is None or den is None or den <= 0:
        return None
    return num / den


def mean(values: Iterable[float]) -> float | None:
    data = list(values)
    return statistics.fmean(data) if data else None


def median(values: Iterable[float]) -> float | None:
    data = list(values)
    return statistics.median(data) if data else None


def percentile(values: Iterable[float], fraction: float) -> float | None:
    data = sorted(values)
    if not data:
        return None
    position = fraction * (len(data) - 1)
    lo, hi = math.floor(position), math.ceil(position)
    if lo == hi:
        return data[lo]
    return data[lo] + (position - lo) * (data[hi] - data[lo])


def geomean_ratio(pairs: Iterable[tuple[float, float]]) -> float | None:
    logs = [math.log(right / left) for left, right in pairs if left > 0 and right > 0]
    return math.exp(statistics.fmean(logs)) if logs else None


def fmt(value: float | None, digits: int = 2) -> str:
    return "N/A" if value is None else f"{value:.{digits}f}"


def is_valid(row: dict[str, str]) -> bool:
    return (
        row.get("scorr_status") == "PASS"
        and row.get("stran_status") == "PASS"
        and row.get("dsec_status") in {"PASS", "SKIP"}
        and row.get("error") in NA
    )


@dataclass
class Run:
    path: Path
    rows: list[dict[str, str]]

    @property
    def label(self) -> str:
        return self.path.stem.removeprefix("stran_root_")

    @property
    def valid(self) -> list[dict[str, str]]:
        return [row for row in self.rows if is_valid(row)]

    @property
    def by_case(self) -> dict[str, dict[str, str]]:
        return {row["file"]: row for row in self.valid}


def load(path: Path) -> Run:
    with path.open("r", encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    if not rows:
        raise ValueError(f"empty CSV: {path}")
    return Run(path=path, rows=rows)


def case_build_gain(row: dict[str, str]) -> float | None:
    return number(row.get("seq_stage_build_and_gain"))


def case_build_pct(row: dict[str, str]) -> float | None:
    value = ratio(case_build_gain(row), row.get("seq_stage_and_before"))
    return None if value is None else 100.0 * value


def print_run_summary(runs: list[Run]) -> None:
    print("\nRun summary (phase=SEQ Build only; weighted time/funnel totals)")
    print("=" * 132)
    print(
        f"{'run':<32} {'pass/all':>9} {'prof':>5} {'SEQ gain':>10} "
        f"{'gain mean/med %':>19} {'SB+':>5} {'SEQ time med/p90 s':>20} "
        f"{'Build med/wtd %':>17} {'enum med/wtd %':>17} {'gen/prv/sel':>22}"
    )
    for run in runs:
        valid = run.valid
        profiled = [
            row for row in valid
            if number(row.get("seq_profile_total_sec")) is not None
        ]
        build_gains = [
            value for row in valid
            if (value := case_build_gain(row)) is not None
        ]
        build_qor = [
            value for row in valid
            if (value := case_build_pct(row)) is not None
        ]
        times = [
            value for row in profiled
            if (value := number(row.get("seq_profile_total_sec"))) is not None
        ]
        profile_total = sum(
            number(row.get("seq_profile_total_sec")) or 0 for row in profiled
        )
        build_time = sum(
            number(row.get("seq_profile_build_discovery_sec")) or 0
            for row in profiled
        )
        enum_time = sum(
            number(row.get("seq_profile_resub_enum_sec")) or 0
            for row in profiled
        )
        build_shares = [
            100.0 * build_seconds / total
            for row in profiled
            if (total := number(row.get("seq_profile_total_sec")))
            and (build_seconds := number(
                row.get("seq_profile_build_discovery_sec")
            )) is not None
        ]
        enum_shares = [
            100.0 * enum / build_seconds
            for row in profiled
            if (build_seconds := number(
                row.get("seq_profile_build_discovery_sec")
            ))
            and (enum := number(
                row.get("seq_profile_resub_enum_sec")
            )) is not None
        ]
        generated = sum(
            number(row.get("seq_stage_build_generated")) or 0 for row in valid
        )
        proved = sum(
            number(row.get("seq_stage_build_proved")) or 0 for row in valid
        )
        selected = sum(
            number(row.get("seq_stage_build_selected")) or 0 for row in valid
        )
        print(
            f"{run.label:<32} {len(valid):>4}/{len(run.rows):<4} {len(profiled):>5} "
            f"{int(sum(build_gains)):>10} "
            f"{fmt(mean(build_qor), 3):>8}/{fmt(median(build_qor), 3):<8} "
            f"{sum(value > 0 for value in build_gains):>5} "
            f"{fmt(median(times)):>8}/{fmt(percentile(times, .9)):<8} "
            f"{fmt(median(build_shares)):>7}/{fmt(100 * build_time / profile_total if profile_total else None):<7} "
            f"{fmt(median(enum_shares)):>7}/{fmt(100 * enum_time / build_time if build_time else None):<7} "
            f"{int(generated):>10}/{int(proved):>6}/{int(selected):<5}"
        )


def compare(reference: Run, candidate: Run) -> None:
    common = sorted(reference.by_case.keys() & candidate.by_case.keys())
    pairs = [(reference.by_case[name], candidate.by_case[name]) for name in common]
    gain_pairs = [
        (left, right, case_build_gain(left), case_build_gain(right))
        for left, right in pairs
    ]
    gain_pairs = [
        item for item in gain_pairs if item[2] is not None and item[3] is not None
    ]
    wins = sum(right_gain > left_gain for _, _, left_gain, right_gain in gain_pairs)
    ties = sum(right_gain == left_gain for _, _, left_gain, right_gain in gain_pairs)
    losses = sum(right_gain < left_gain for _, _, left_gain, right_gain in gain_pairs)
    runtime_ratio = geomean_ratio(
        (
            number(left.get("seq_profile_total_sec")) or 0,
            number(right.get("seq_profile_total_sec")) or 0,
        )
        for left, right in pairs
    )
    discovery_ratio = geomean_ratio(
        (
            number(left.get("seq_profile_build_discovery_sec")) or 0,
            number(right.get("seq_profile_build_discovery_sec")) or 0,
        )
        for left, right in pairs
    )
    gain_delta = [
        right_gain - left_gain
        for _, _, left_gain, right_gain in gain_pairs
    ]
    build_delta = [
        right_build - left_build
        for left, right in pairs
        if (left_build := case_build_pct(left)) is not None
        and (right_build := case_build_pct(right)) is not None
    ]
    build_pos_left = {
        name for name in common
        if (case_build_gain(reference.by_case[name]) or 0) > 0
    }
    build_pos_right = {
        name for name in common
        if (case_build_gain(candidate.by_case[name]) or 0) > 0
    }
    print(f"\n{candidate.label}  vs  {reference.label}  (common PASS n={len(common)})")
    print("-" * 110)
    print(
        f"SEQ Build gain candidate better/tie/worse = {wins}/{ties}/{losses}; "
        f"mean absolute gain delta = {fmt(mean(gain_delta), 3)} AND; "
        f"mean normalized gain delta = {fmt(mean(build_delta), 3)} pp"
    )
    print(
        f"SEQ-phase runtime geometric ratio = {fmt(runtime_ratio, 3)}x; "
        f"SEQ Build-discovery geometric ratio = {fmt(discovery_ratio, 3)}x; "
        f"SEQ-Build-positive gained/lost = {len(build_pos_right - build_pos_left)}/"
        f"{len(build_pos_left - build_pos_right)}"
    )


def ranked_cases(runs: list[Run], top: int) -> None:
    records: dict[str, list[tuple[Run, dict[str, str]]]] = {}
    for run in runs:
        for case, row in run.by_case.items():
            if number(row.get("seq_profile_total_sec")) is not None:
                records.setdefault(case, []).append((run, row))

    useful = []
    waste = []
    for case, observations in records.items():
        best_build = max((case_build_pct(row) or 0) for _, row in observations)
        max_gain = max(case_build_gain(row) or 0 for _, row in observations)
        min_runtime = min(
            number(row.get("seq_profile_total_sec")) or math.inf
            for _, row in observations
        )
        max_build_time = max(
            number(row.get("seq_profile_build_discovery_sec")) or 0
            for _, row in observations
        )
        if best_build > 0:
            useful.append((best_build, max_gain, min_runtime, case))
        elif max_build_time > 0:
            waste.append((max_build_time, min_runtime, case))
    useful.sort(key=lambda item: (-item[0], -item[1], item[2], item[3]))
    waste.sort(key=lambda item: (-item[0], item[1], item[2]))

    print(f"\nTop {top} SEQ-Build-positive cases (union across runs)")
    print("=" * 100)
    for build_pct, gain, runtime, case in useful[:top]:
        print(f"{build_pct:8.3f}%  gain={int(gain):>7}  fastest={runtime:>9.2f}s  {case}")
    print(f"\nTop {top} expensive zero-SEQ-Build cases (profiling controls)")
    print("=" * 100)
    for build_time, runtime, case in waste[:top]:
        print(f"Build={build_time:>10.2f}s  fastest={runtime:>9.2f}s  {case}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csv", nargs="+", type=Path)
    parser.add_argument("--top", type=int, default=12)
    parser.add_argument(
        "--pairs",
        action="store_true",
        help="compare each run with the preceding run in the command line",
    )
    parser.add_argument(
        "--reference-first",
        action="store_true",
        help="compare every later run with the first run",
    )
    args = parser.parse_args()
    runs = [load(path.expanduser().resolve()) for path in args.csv]
    print_run_summary(runs)
    if args.pairs:
        for reference, candidate in zip(runs, runs[1:]):
            compare(reference, candidate)
    if args.reference_first and len(runs) > 1:
        for candidate in runs[1:]:
            compare(runs[0], candidate)
    ranked_cases(runs, args.top)


if __name__ == "__main__":
    main()
