#!/usr/bin/env python3
"""Compare matched raw batches, with per-circuit runtime statistics on stdout."""

import argparse
import csv
import json
import math
import statistics
from collections import Counter
from pathlib import Path


def number(row, key):
    value = row[key]
    if value in ("", "N/A"):
        raise ValueError(f"Missing {key} for {row['file']}")
    result = float(value)
    if not math.isfinite(result):
        raise ValueError(f"Non-finite {key} for {row['file']}")
    return result


def passed(row):
    return (row["scorr_status"] == row["stran_status"] == "PASS"
            and row["dsec_status"] in ("SKIP", "PASS")
            and row.get("error") in (None, "", "N/A"))


def read(path, basename=False):
    with Path(path).open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    if not rows:
        raise ValueError(f"Empty batch: {path}")
    for line, row in enumerate(rows, start=2):
        if None in row or any(value is None for value in row.values()):
            raise ValueError(f"Malformed CSV row {line} in {path}")
    data = {(Path(row["file"]).name if basename else row["file"]): row for row in rows}
    if len(data) != len(rows):
        raise ValueError(f"Duplicate input keys in {path}")
    return data


def totals(rows, keys):
    return {key: sum(number(row, key) for row in rows) for key in keys}


def speedup(base, data, keys, metric):
    ratios = [number(base[key], metric) / number(data[key], metric)
              for key in keys if number(data[key], metric) > 0
              and number(base[key], metric) > 0]
    return distribution(ratios)


def distribution(values):
    return {"cases": len(values),
            "mean": statistics.fmean(values) if values else None,
            "median": statistics.median(values) if values else None,
            "geomean": statistics.geometric_mean(values)
            if values and all(v > 0 for v in values) else None,
            "negative": sum(v < 0 for v in values)}


def relative_scorr(reference, data, keys, per_case=False):
    """Apply the user's approximation: mean_i(T2_i / Tscorr_i - 1)."""
    result = {"formula": "stran2: pipeline/scorr - 1; scorr-stran: stran/scorr",
              "note": "Approximation using paired standalone scorr; negatives are not clamped.",
              "timing": {}, "qor": {}}
    for suffix in ("time_ms", "user_ms"):
        ratios, seconds, cases = [], [], []
        for key in keys:
            base, row = reference[key], data[key]
            if not passed(base) or not passed(row):
                raise ValueError(f"Non-PASS case: {key}")
            if base["input_sha256"] != row["input_sha256"]:
                raise ValueError(f"Input content differs: {key}")
            if base["flow"] != "scorr-stran":
                raise ValueError("scorr reference must be a scorr-stran run")
            denominator = number(base, "scorr_" + suffix)
            if denominator <= 0:
                raise ValueError(f"Nonpositive scorr time: {key}")
            if row["flow"] == "stran2":
                if base["scorr_args"].strip():
                    raise ValueError("Integrated stran2 requires default scorr reference")
                elapsed = number(row, "pipeline_" + suffix) - denominator
            elif row["flow"] == "scorr-stran":
                if row["scorr_args"] != base["scorr_args"]:
                    raise ValueError(f"Different scorr configuration: {key}")
                elapsed = number(row, "stran_" + suffix)
            else:
                raise ValueError(f"Unknown flow: {row['flow']}")
            ratio = elapsed / denominator
            ratios.append(ratio)
            seconds.append(elapsed / 1000)
            if per_case:
                cases.append({"file": key, "extra_ratio": ratio,
                              "extra_seconds_estimate": elapsed / 1000})
        result["timing"][suffix] = {"extra_ratio": distribution(ratios),
                                    "extra_seconds_estimate": distribution(seconds)}
        if per_case:
            result["timing"][suffix]["per_case"] = cases
    for metric in ("and", "latches"):
        changes = [number(reference[k], "scorr_" + metric)
                   - number(data[k], "stran_" + metric) for k in keys]
        counts = Counter("better" if v > 0 else "worse" if v < 0 else "equal"
                         for v in changes)
        base_count = sum(number(reference[k], "scorr_" + metric) for k in keys)
        result["qor"][metric] = {"extra_reduction": sum(changes),
            "percent_of_scorr_count": 100 * sum(changes) / base_count if base_count else None,
            "cases": dict(counts)}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline")
    parser.add_argument("candidates", nargs="+")
    parser.add_argument("--basename", action="store_true", help="pair renamed probe symlinks; input hashes must match")
    parser.add_argument("--extra-metric", action="append", default=[],
                        help="report optional numeric metric with its own presence count")
    parser.add_argument("--relative-scorr", action="store_true",
                        help="use baseline's standalone scorr; subtract 1 for integrated stran2")
    parser.add_argument("--per-case", action="store_true",
                        help="include each circuit's relative-scorr time in stdout JSON")
    args = parser.parse_args()
    paths = [args.baseline, *args.candidates]
    datasets = [read(path, args.basename) for path in paths]
    keys = sorted(set.intersection(*(set(data) for data in datasets)))
    for key in keys:
        if len({data[key]["input_sha256"] for data in datasets}) != 1:
            raise ValueError(f"Input content differs for {key}")
    matched = [key for key in keys if all(passed(data[key]) for data in datasets)]
    metrics = [
        "source_and", "stran_and", "stran_latches", "pipeline_time_ms",
        "pipeline_user_ms", "profile_total_sec", "profile_build_discovery_sec",
        "profile_divisor_discovery_sec", "profile_resub_enum_sec",
        "profile_seq_proof_shared_sec", "profile_comb_proof_sec", "profile_selection_sec",
        "profile_root_refresh_sec", "profile_commit_sec", "profile_sim_sec",
        "seq_stage_and_gain", "seq_build_ordered_and_gain",
        "seq_stage_build_generated", "seq_stage_build_proved", "seq_stage_build_selected",
        "seq_profile_build_discovery_sec", "seq_profile_divisor_discovery_sec",
        "seq_profile_resub_enum_sec", "seq_profile_resub_init_sec",
        "root_build_horizon_eligible_roots", "root_build_horizon_zero_accepted_roots",
    ]
    exact = ["stran_and", "stran_latches", "seq_stage_and_gain",
             "seq_build_ordered_and_gain", "seq_stage_build_generated",
             "seq_stage_build_proved", "seq_stage_build_selected",
             "comb_stage_build_generated", "comb_stage_build_proved",
             "comb_stage_build_selected"]
    pass_keys = matched
    required = set(metrics + exact)
    matched = [key for key in pass_keys if all(
        all(data[key].get(field) not in (None, "", "N/A") for field in required)
        for data in datasets)]
    basic = ["source_and", "source_latches", "stran_and", "stran_latches",
             "pipeline_time_ms", "pipeline_user_ms"]
    basic_keys = [key for key in pass_keys if all(
        all(data[key].get(field) not in (None, "", "N/A") for field in basic)
        for data in datasets)]
    result = {"matched_all_pass": len(pass_keys), "matched_profiled": len(matched),
              "excluded_missing_metrics": sorted(set(pass_keys) - set(matched)),
              "shared_inputs": len(keys), "runs": []}
    for path, data in zip(paths, datasets):
        rows = [data[key] for key in matched]
        base = datasets[0]
        item = {"path": str(path), "rows": len(data), "status": {},
                "provenance": {field: sorted({row[field] for row in data.values()})
                               for field in ("git_commit", "git_dirty", "abc_sha256",
                                             "script_sha256", "profile_parser_sha256",
                                             "input_count", "input_manifest_id", "stran_args")}}
        for field in ("scorr_status", "stran_status", "dsec_status"):
            item["status"][field] = dict(Counter(row[field] for row in data.values()))
        item["nonempty_error_rows"] = sum(
            row.get("error") not in (None, "", "N/A") for row in data.values())
        if args.relative_scorr:
            item["relative_scorr"] = relative_scorr(base, data, pass_keys, args.per_case)
        item["extra_metrics"] = {}
        for field in args.extra_metric:
            values = [number(data[key], field) for key in pass_keys
                      if data[key].get(field) not in (None, "", "N/A")]
            item["extra_metrics"][field] = {
                "cases": len(values), "missing": len(pass_keys) - len(values),
                "total": sum(values) if values else None,
                "min": min(values) if values else None,
                "max": max(values) if values else None,
            }
        item["basic_matched"] = len(basic_keys)
        item["all_pass_basic_totals"] = basic_sums = totals([data[key] for key in basic_keys], basic)
        item["all_pass_speedup"] = {metric: speedup(base, data, basic_keys, metric)
                                    for metric in ("pipeline_time_ms", "pipeline_user_ms")}
        item["all_pass_final_count_mismatch"] = {
            metric: sum(number(base[key], metric) != number(data[key], metric)
                        for key in basic_keys) for metric in ("stran_and", "stran_latches")}
        for metric in ("and", "latches"):
            before, after = basic_sums["source_" + metric], basic_sums["stran_" + metric]
            basic_sums["reduction_" + metric] = before - after
            basic_sums["reduction_" + metric + "_pct"] = 100 * (before - after) / before if before else None
        item["totals"] = sums = totals(rows, metrics)
        for gain in ("seq_stage_and_gain", "seq_build_ordered_and_gain"):
            sums[gain + "_pct"] = 100 * sums[gain] / sums["source_and"] if sums["source_and"] else None
        diag = [key for key in next(iter(data.values()))
                if key.startswith("root_seq_preprocess_exp_")]
        if diag and all(all(row[field] not in ("", "N/A") for field in diag) for row in rows):
            item["seq_diagnostics"] = d = totals(rows, diag)
            prefix = "root_seq_preprocess_exp_"
            for label, numerator, denominator in [
                ("pool_conflict_pct", "obs_conflict", "obs_roots"),
                ("reservoir_conflict_pct", "full_conflict", "full_roots"),
                ("unique_observation_pct", "obs_unique", "obs_total"),
            ]:
                if d[prefix + denominator]:
                    d[label] = 100 * d[prefix + numerator] / d[prefix + denominator]
            for category in ("build", "rank"):
                zero = d[prefix + f"zero_{category}_sec"]
                positive = d[prefix + f"positive_{category}_sec"]
                if zero + positive:
                    d[f"zero_{category}_time_pct"] = 100 * zero / (zero + positive)
        if matched:
            for time in ("pipeline_time_ms", "pipeline_user_ms"):
                item[time + "_geomean_speedup"] = speedup(base, data, matched, time)["geomean"]
            item["exact_count_mismatch"] = {
                metric: sum(number(base[key], metric) != number(data[key], metric)
                            for key in matched) for metric in exact}
            item["qor_cases"] = {}
            for metric in ("stran_and", "seq_stage_and_gain", "seq_build_ordered_and_gain"):
                counts = Counter()
                for key in matched:
                    change = number(data[key], metric) - number(base[key], metric)
                    if metric == "stran_and":
                        change = -change
                    counts["better" if change > 0 else "worse" if change < 0 else "equal"] += 1
                item["qor_cases"][metric] = dict(counts)
            item["largest_wall_savings"] = sorted(
                [(key, number(base[key], "pipeline_time_ms") - number(data[key], "pipeline_time_ms"))
                 for key in matched], key=lambda pair: -pair[1])[:5]
            item["largest_wall_regressions"] = sorted(
                [(key, number(data[key], "pipeline_time_ms") - number(base[key], "pipeline_time_ms"))
                 for key in matched], key=lambda pair: -pair[1])[:5]
        result["runs"].append(item)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
