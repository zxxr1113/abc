#!/usr/bin/env python3
"""Summarize schema-6 &stran Build-discovery funnels and outcome buckets."""

from __future__ import annotations

import argparse
import csv
import statistics
from pathlib import Path


def num(value: object) -> float | None:
    try:
        return float(value)  # type: ignore[arg-type]
    except (TypeError, ValueError):
        return None


def token(value: str) -> str:
    return value.replace("-", "_").replace("+", "plus")


def load(path: Path) -> list[dict[str, str]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    return [
        row for row in rows
        if row.get("stran_status") == "PASS"
        and (num(row.get("profile_schema")) or 0) >= 6
    ]


def total(rows: list[dict[str, str]], field: str) -> float:
    return sum(num(row.get(field)) or 0 for row in rows)


def pct(numerator: float, denominator: float) -> str:
    return "N/A" if denominator <= 0 else f"{100.0 * numerator / denominator:.4f}%"


def bucket_table(
    rows: list[dict[str, str]], family: str, buckets: tuple[str, ...],
    include_time: bool = False,
) -> None:
    records = []
    for bucket in buckets:
        prefix = f"root_build_{family}_{token(bucket)}"
        generated = total(rows, f"{prefix}_generated")
        proved = total(rows, f"{prefix}_proved")
        selected = total(rows, f"{prefix}_selected")
        selected_gain = total(rows, f"{prefix}_selected_and_gain")
        valid = total(rows, f"{prefix}_valid") if include_time else generated
        accepted = total(rows, f"{prefix}_accepted") if include_time else generated
        seconds = total(rows, f"{prefix}_time_sec") if include_time else 0
        records.append((
            bucket, valid, accepted, generated, proved, selected,
            selected_gain, seconds,
        ))
    all_generated = sum(record[3] for record in records)
    all_selected_gain = sum(record[6] for record in records)
    cumulative_generated = cumulative_selected_gain = 0.0
    print(f"\n{family} buckets (weighted candidate totals)")
    print("-" * 112)
    if include_time:
        print(
            f"{'bucket':<12} {'valid':>12} {'accepted':>12} {'generated':>12} "
            f"{'proved':>10} {'selected':>10} {'sel gain':>10} "
            f"{'proof/gen':>11} {'sel/gen':>11} {'time s':>10}"
        )
    else:
        print(
            f"{'bucket':<12} {'generated':>12} {'proved':>10} {'selected':>10} "
            f"{'sel gain':>10} {'proof/gen':>11} {'sel/gen':>11} "
            f"{'cum gen':>10} {'cum gain':>10}"
        )
    for (bucket, valid, accepted, generated, proved, selected,
         selected_gain, seconds) in records:
        cumulative_generated += generated
        cumulative_selected_gain += selected_gain
        if include_time:
            print(
                f"{bucket:<12} {int(valid):>12,} {int(accepted):>12,} "
                f"{int(generated):>12,} {int(proved):>10,} {int(selected):>10,} "
                f"{int(selected_gain):>10,} "
                f"{pct(proved, generated):>11} {pct(selected, generated):>11} "
                f"{seconds:>10.3f}"
            )
        else:
            print(
                f"{bucket:<12} {int(generated):>12,} {int(proved):>10,} "
                f"{int(selected):>10,} {int(selected_gain):>10,} "
                f"{pct(proved, generated):>11} "
                f"{pct(selected, generated):>11} "
                f"{pct(cumulative_generated, all_generated):>10} "
                f"{pct(cumulative_selected_gain, all_selected_gain):>10}"
            )


def mffc_table(rows: list[dict[str, str]]) -> None:
    print("\nMFFC buckets (discovery work by root-call)")
    print("-" * 88)
    print(
        f"{'bucket':<12} {'calls':>12} {'iterator next':>16} {'accepted':>12} "
        f"{'accept/next':>13} {'time s':>12}"
    )
    for bucket in ("1", "2", "3-4", "5-8", "9-16", "17+"):
        prefix = f"root_build_mffc_{token(bucket)}"
        calls = total(rows, f"{prefix}_calls")
        next_count = total(rows, f"{prefix}_next")
        accepted = total(rows, f"{prefix}_accepted")
        seconds = total(rows, f"{prefix}_time_sec")
        print(
            f"{bucket:<12} {int(calls):>12,} {int(next_count):>16,} "
            f"{int(accepted):>12,} {pct(accepted, next_count):>13} "
            f"{seconds:>12.3f}"
        )


def report(path: Path) -> None:
    rows = load(path)
    if not rows:
        raise SystemExit(f"[ERROR] no PASS schema-6 rows in {path}")
    iterator_next = total(rows, "root_build_iterator_next")
    accepted = total(rows, "root_build_accepted")
    build_shares = [
        value for row in rows
        if (value := num(row.get("profile_build_discovery_pct"))) is not None
    ]
    print(f"\n{path}  (PASS schema-6 cases={len(rows)})")
    print("=" * 112)
    print(
        f"iterator-next={int(iterator_next):,} accepted={int(accepted):,} "
        f"accept/next={pct(accepted, iterator_next)} "
        f"MFFC=1 skipped={int(total(rows, 'root_build_mffc_one_skipped')):,} "
        f"median Build/runtime={statistics.median(build_shares):.2f}%"
    )
    for field in (
        "semantic_invalid", "collapsed_direct", "reject_nonpositive",
        "reject_known", "reject_direct", "reject_page",
    ):
        value = total(rows, f"root_build_{field}")
        print(f"  {field:<20} {int(value):>14,}  {pct(value, iterator_next):>10}")

    bucket_table(rows, "stage", ("one-gate", "div-gate", "gate-gate", "greedy"), True)
    bucket_table(rows, "rank", ("1", "2", "3-4", "5-8", "9-16", "17-32", "33-64", "65+"))
    bucket_table(rows, "gates", ("1", "2", "3", "4", "5-8", "9+"))
    bucket_table(rows, "gain", ("1", "2", "3-4", "5-8", "9-16", "17+"))
    bucket_table(rows, "divrank", ("1-4", "5-8", "9-16", "17-32", "33-64", "65+"))
    mffc_table(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csv", nargs="+", type=Path)
    args = parser.parse_args()
    for path in args.csv:
        report(path.expanduser().resolve())


if __name__ == "__main__":
    main()
