#!/usr/bin/env python3
"""Terminal report of &stran proved/selected ratios and reduction percentages.

Crosses the two classification axes the profiler emits:

  * proof stage    -- comb (combinationally proved) vs seq (proved by scorr)
  * candidate kind -- constant / existing / constructed (a.k.a. Build)

For every (stage, kind) cell this shows ``selected/newly-proved`` event counts,
their ratio, and the input-normalized reduction percentage.  A selected
relation can come from remapped proof history, so the ratio may exceed 100%;
``history-selected`` is reported separately and this is not treated as an
invariant violation.
Stage rollups (comb/seq totals) and the OVERALL row are computed from raw
counts, so ratios are ``sum(selected)/sum(proved)`` and never an average of
per-case percentages.

Input is the CSV written by ``bench_scorr_then_stran.py`` (with ``&stran -p``).
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path
from typing import Any

from analyze_stran_stage_profile import KINDS, STAGES, make_case, number

NA = "N/A"
KIND_LABEL = {"constant": "C", "existing": "E", "constructed": "B"}


def as_num(value: Any) -> float | None:
    return number(value)


def ratio_pct(num: Any, den: Any) -> float | None:
    n, d = as_num(num), as_num(den)
    if n is None or d is None or d == 0:
        return None
    return 100.0 * n / d


def fmt_int(value: Any) -> str:
    parsed = as_num(value)
    return f"{int(parsed)}" if parsed is not None else "·"


def fmt_pct(value: Any, digits: int = 2) -> str:
    parsed = as_num(value)
    return f"{parsed:.{digits}f}%" if parsed is not None else "·"


def fmt_ratio(value: Any) -> str:
    parsed = as_num(value)
    return f"{parsed:.1f}%" if parsed is not None else "·"


def build_case(source: dict[str, str]) -> dict[str, Any] | None:
    profile = make_case(source)
    if profile["status"] != "PASS":
        return None
    out: dict[str, Any] = {
        "case": profile["case"],
        "input_and": as_num(profile["input_and"]),
        "comb_reduction_pct": as_num(profile["comb_reduction_pct"]),
        "seq_reduction_pct": as_num(profile["seq_reduction_pct"]),
        "total_reduction_pct": as_num(profile["total_reduction_pct"]),
        "comb_gain": as_num(profile["comb_reduced_and"]),
        "seq_gain": as_num(profile["seq_reduced_and"]),
        "total_gain": as_num(profile["total_reduced_and"]),
        "new_proved": as_num(source.get("root_new_proved")),
        "history_selected": as_num(source.get("root_history_proved_selected")),
    }
    for stage in STAGES:
        proved = sum(as_num(profile[f"{stage}_{k}_proved"]) or 0 for k in KINDS)
        selected = sum(as_num(profile[f"{stage}_{k}_selected"]) or 0 for k in KINDS)
        out[f"{stage}_proved"] = proved
        out[f"{stage}_selected"] = selected
        out[f"{stage}_ratio"] = ratio_pct(selected, proved)
        for kind in KINDS:
            proved = as_num(profile[f"{stage}_{kind}_proved"])
            selected = as_num(profile[f"{stage}_{kind}_selected"])
            out[f"{stage}_{kind}_proved"] = proved
            out[f"{stage}_{kind}_selected"] = selected
            out[f"{stage}_{kind}_ratio"] = ratio_pct(selected, proved)
            out[f"{stage}_{kind}_reduction_pct"] = as_num(
                profile[f"{stage}_{kind}_reduction_pct"])
            out[f"{stage}_{kind}_gain"] = as_num(
                profile[f"{stage}_{kind}_and_gain"])
    return out


def build_overall(cases: list[dict[str, Any]]) -> dict[str, Any]:
    overall: dict[str, Any] = {
        "case": "OVERALL", "input_and": 0.0,
        "comb_gain": 0.0, "seq_gain": 0.0, "total_gain": 0.0,
        "new_proved": 0.0, "history_selected": 0.0,
    }
    for stage in STAGES:
        overall[f"{stage}_proved"] = 0
        overall[f"{stage}_selected"] = 0
        for kind in KINDS:
            overall[f"{stage}_{kind}_proved"] = 0
            overall[f"{stage}_{kind}_selected"] = 0
            overall[f"{stage}_{kind}_gain"] = 0.0
    for case in cases:
        for key in (
            "input_and", "comb_gain", "seq_gain", "total_gain",
            "new_proved", "history_selected",
        ):
            overall[key] += case[key] or 0.0
        for stage in STAGES:
            overall[f"{stage}_proved"] += case[f"{stage}_proved"] or 0
            overall[f"{stage}_selected"] += case[f"{stage}_selected"] or 0
            for kind in KINDS:
                overall[f"{stage}_{kind}_proved"] += case[f"{stage}_{kind}_proved"] or 0
                overall[f"{stage}_{kind}_selected"] += case[f"{stage}_{kind}_selected"] or 0
                overall[f"{stage}_{kind}_gain"] += case[f"{stage}_{kind}_gain"] or 0.0
    for stage in STAGES:
        overall[f"{stage}_ratio"] = ratio_pct(
            overall[f"{stage}_selected"], overall[f"{stage}_proved"])
        for kind in KINDS:
            overall[f"{stage}_{kind}_ratio"] = ratio_pct(
                overall[f"{stage}_{kind}_selected"], overall[f"{stage}_{kind}_proved"])
            overall[f"{stage}_{kind}_reduction_pct"] = ratio_pct(
                overall[f"{stage}_{kind}_gain"], overall["input_and"])
    overall["comb_reduction_pct"] = ratio_pct(
        overall["comb_gain"], overall["input_and"])
    overall["seq_reduction_pct"] = ratio_pct(
        overall["seq_gain"], overall["input_and"])
    overall["total_reduction_pct"] = ratio_pct(
        overall["total_gain"], overall["input_and"])
    return overall


def clip(text: str, width: int) -> str:
    if len(text) <= width:
        return text
    tail = min(16, max(9, width // 3))
    head = width - tail - 1
    return text[:head] + "…" + text[-tail:]


def kind_line(case: dict[str, Any], stage: str) -> str:
    cells = []
    for kind in KINDS:
        label = KIND_LABEL[kind]
        cells.append(
            f"{label} {fmt_int(case[f'{stage}_{kind}_selected'])}/"
            f"{fmt_int(case[f'{stage}_{kind}_proved'])}"
            f" ({fmt_ratio(case[f'{stage}_{kind}_ratio'])})"
            f" r={fmt_pct(case[f'{stage}_{kind}_reduction_pct'])}"
        )
    return "  ".join(cells)


def render_table(rows: list[dict[str, Any]], case_width: int) -> str:
    header = (
        f"{'Rank':>4}  {'Case':<{case_width}} | {'Input':>7} | "
        f"{'Comb%':>7} {'Seq%':>7} {'Total%':>7} | "
        f"{'Comb sel/new':>13} {'ratio':>7} | "
        f"{'Seq sel/new':>12} {'ratio':>7} | {'Hist sel':>8}"
    )
    sep = "-" * len(header)
    lines = [header, sep]
    for rank, case in enumerate(rows, start=1):
        name = clip(Path(str(case["case"])).name, case_width)
        comb = f"{fmt_int(case['comb_selected'])}/{fmt_int(case['comb_proved'])}"
        seq = f"{fmt_int(case['seq_selected'])}/{fmt_int(case['seq_proved'])}"
        lines.append(
            f"{rank:>4}  {name:<{case_width}} | {fmt_int(case['input_and']):>7} | "
            f"{fmt_pct(case['comb_reduction_pct']):>7} "
            f"{fmt_pct(case['seq_reduction_pct']):>7} "
            f"{fmt_pct(case['total_reduction_pct']):>7} | "
            f"{comb:>13} {fmt_ratio(case['comb_ratio']):>7} | "
            f"{seq:>12} {fmt_ratio(case['seq_ratio']):>7} | "
            f"{fmt_int(case['history_selected']):>8}"
        )
        lines.append(f"      comb: {kind_line(case, 'comb')}")
        lines.append(f"      seq : {kind_line(case, 'seq')}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="&stran proved/selected ratios and reduction percentages")
    parser.add_argument("csv", type=Path, help="bench_scorr_then_stran.py output")
    parser.add_argument("--top", type=int, default=30,
                        help="cases to print (0 = all)")
    parser.add_argument("--case-width", type=int, default=40,
                        help="case-name column width (min 20)")
    args = parser.parse_args()
    if args.top < 0:
        sys.exit("[ERROR] --top must be nonnegative")
    if args.case_width < 20:
        sys.exit("[ERROR] --case-width must be at least 20")

    path = args.csv.expanduser().resolve()
    with path.open("r", encoding="utf-8", newline="") as handle:
        source_rows = list(csv.DictReader(handle))
    if not source_rows:
        sys.exit(f"[ERROR] empty CSV: {path}")

    required = {f"{stage}_{kind}_proved" for stage in STAGES for kind in KINDS}
    missing = sorted(required - set(source_rows[0]))
    if missing:
        sys.exit(
            "[ERROR] CSV has no stage-kind profiling columns; rebuild ABC and "
            "rerun bench_scorr_then_stran.py with &stran -p. Missing: "
            + ", ".join(missing))

    cases: list[dict[str, Any]] = []
    invalid = 0
    for source in source_rows:
        case = build_case(source)
        if case is None:
            invalid += 1
        else:
            cases.append(case)
    if not cases:
        sys.exit("[ERROR] no valid cases")

    cases.sort(key=lambda c: c["total_reduction_pct"] or 0.0, reverse=True)
    shown = cases if args.top == 0 else cases[: args.top]
    overall = build_overall(cases)

    print()
    print(f"&stran proof / reduction report — {path.name}")
    print(
        f"valid={len(cases)}  invalid={invalid}  "
        f"sorted by total reduction % (of input ANDs), descending"
    )
    print(
        "proved=newly proved in the current snapshot; history-selected is "
        "remapped formal proof reuse, so sel/new may exceed 100%"
    )
    print()
    print(render_table(shown, args.case_width), end="")

    comb = f"{fmt_int(overall['comb_selected'])}/{fmt_int(overall['comb_proved'])}"
    seq = f"{fmt_int(overall['seq_selected'])}/{fmt_int(overall['seq_proved'])}"
    print(f"{'OVERALL':<{args.case_width}} aggregated over {len(cases)} valid cases")
    print(
        f"{'':<{args.case_width}} | {fmt_int(overall['input_and']):>7} | "
        f"{fmt_pct(overall['comb_reduction_pct']):>7} "
        f"{fmt_pct(overall['seq_reduction_pct']):>7} "
        f"{fmt_pct(overall['total_reduction_pct']):>7} | "
        f"{comb:>13} {fmt_ratio(overall['comb_ratio']):>7} | "
        f"{seq:>12} {fmt_ratio(overall['seq_ratio']):>7} | "
        f"{fmt_int(overall['history_selected']):>8}"
    )
    print(f"      comb: {kind_line(overall, 'comb')}")
    print(f"      seq : {kind_line(overall, 'seq')}")
    print()


if __name__ == "__main__":
    main()
