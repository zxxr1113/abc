#!/usr/bin/env python3
"""Match exact candidate identities and locate their first partition loss."""

import argparse
import json
from collections import Counter
from pathlib import Path


def read_trace(path):
    batches = {}
    for line_no, line in enumerate(Path(path).read_text().splitlines(), 1):
        if not line.startswith("stran-quality-"):
            continue
        if line.startswith("stran-quality-select:"):
            continue
        prefix, payload = line.split(": ", 1)
        values = dict(token.split("=", 1) for token in payload.split())
        batch = batches.setdefault(int(values["batch"]), {
            "info": {}, "candidates": {}, "results": {}, "classes": [], "sat": []})
        values["line"] = line_no
        if prefix == "stran-quality-class":
            values["pairs"] = dict(tuple(map(int, pair.split(":")))
                                   for pair in values["pairs"].split(",") if pair)
            values["round"] = int(values["round"])
            batch["classes"].append(values)
        else:
            values = {k: v if k in ("recipe", "point") else int(v)
                      for k, v in values.items()}
            if prefix == "stran-quality-batch":
                batch["info"] = values
            elif prefix == "stran-quality-cand":
                values["recipe"] = tuple(map(int, values["recipe"].split(","))) \
                    if values["recipe"] != "-" else ()
                assert values["slot"] not in batch["candidates"]
                batch["candidates"][values["slot"]] = values
            elif prefix == "stran-quality-result":
                assert values["slot"] not in batch["results"]
                batch["results"][values["slot"]] = values
            elif prefix == "stran-quality-sat":
                batch["sat"].append(values)
            else:
                raise ValueError(f"Unknown trace record at {path}:{line_no}")
    for batch in batches.values():
        assert len(batch["candidates"]) == batch["info"]["helpers"] + batch["info"]["cands"]
        assert len(batch["results"]) == batch["info"]["cands"]
    return batches


def identity(c):
    return c["target"], c["kind"], c["out"], c["recipe"]


def head(partition, obj):
    seen = set()
    while obj in partition:
        assert obj not in seen
        seen.add(obj)
        obj = partition[obj]
    return obj


def first_loss(batch, c):
    a, b = c["a"] // 2, c["b"] // 2
    last = None
    for state in batch["classes"]:
        partition = state["pairs"]
        if head(partition, a) != head(partition, b):
            loss = {k: v for k, v in state.items() if k != "pairs"}
            loss["endpoints"] = [a, b]
            loss["heads"] = [head(partition, a), head(partition, b)]
            if last:
                root = head(last["pairs"], a)
                members = {x for x in last["pairs"] if head(last["pairs"], x) == root} | {root}
                loss["previous_class_size"] = len(members)
                events = [s for s in batch["sat"] if s["round"] == state["round"]
                          and (s["a"] in members or s["b"] in members)]
                loss["class_obligation_statuses"] = dict(Counter(s["status"] for s in events))
                loss["endpoint_obligations"] = [s for s in events
                    if s["a"] in (a, b) or s["b"] in (a, b)]
            return loss
        last = state
    return None


def compare(before, after):
    assert before["info"]["and"] == after["info"]["and"]
    assert before["info"]["regs"] == after["info"]["regs"]
    old = {identity(c): c for c in before["candidates"].values() if not c["helper"]}
    new = {identity(c): c for c in after["candidates"].values() if not c["helper"]}
    assert len(old) == before["info"]["cands"]
    assert len(new) == after["info"]["cands"]
    lost = []
    for key, c in old.items():
        if not before["results"][c["slot"]]["proved"]:
            continue
        d = new.get(key)
        if d and after["results"][d["slot"]]["proved"]:
            continue
        lost.append({"before": c, "after": d,
                     "loss": first_loss(after, d) if d else "not-in-this-batch"})
    return {"before": before["info"], "after": after["info"],
            "common": len(old.keys() & new.keys()),
            "before_only": len(old.keys() - new.keys()),
            "after_only": len(new.keys() - old.keys()),
            "lost_proved": lost}


def read_selections(path, and_count):
    selected = []
    for line in Path(path).read_text().splitlines():
        if not line.startswith("stran-quality-select:"):
            continue
        values = dict(token.split("=", 1) for token in line.split(": ", 1)[1].split())
        if int(values["and"]) != and_count:
            continue
        values = {k: v if k == "recipe" else int(v) for k, v in values.items()}
        values["recipe"] = tuple(map(int, values["recipe"].split(","))) \
            if values["recipe"] != "-" else ()
        selected.append(values)
    return selected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before")
    parser.add_argument("after")
    parser.add_argument("--before-batch", type=int, default=2)
    parser.add_argument("--after-batch", type=int, default=2)
    parser.add_argument("--prefix-batches", type=int)
    parser.add_argument("--selection-and", type=int)
    args = parser.parse_args()
    b, a = read_trace(args.before), read_trace(args.after)
    if args.prefix_batches:
        result = {"prefix": []}
        for i in range(1, args.prefix_batches + 1):
            left, right = b[i], a[i]
            result["prefix"].append({
                "batch": i, "before": left["info"], "after": right["info"],
                "ordered_candidates_equal": [identity(c) for c in left["candidates"].values()] ==
                    [identity(c) for c in right["candidates"].values()],
                "proof_results_equal": [(v["proved"], v["lane"]) for v in left["results"].values()] ==
                    [(v["proved"], v["lane"]) for v in right["results"].values()]})
    else:
        result = compare(b[args.before_batch], a[args.after_batch])
    if args.selection_and is not None:
        left = read_selections(args.before, args.selection_and)
        right = read_selections(args.after, args.selection_and)
        lk, rk = {identity(c) for c in left}, {identity(c) for c in right}
        result["selection"] = {
            "before_count": len(left), "after_count": len(right),
            "before_marginal": sum(c["gain"] for c in left),
            "after_marginal": sum(c["gain"] for c in right),
            "before_only": [c for c in left if identity(c) not in rk],
            "after_only": [c for c in right if identity(c) not in lk]}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
