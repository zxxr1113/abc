#!/usr/bin/env python3
"""Exhaustively test necessary trace clauses with candidate-dependent RO inputs.

All 256 functions h(en,a,data) are checked against clauses learned from failed
stateful functions. A clause refers to the failed candidate's trajectory;
the tested h runs its OWN trajectory. No equality of their states is assumed.
"""
import itertools
import json
import sys
from pathlib import Path


def run(table, trace):
    valid = data = 0
    outputs, points, roots, states = [], [], [], []
    for en, a in trace:
        point = en | (a << 1) | (data << 2)
        root = (table >> point) & 1 if table is not None else en & a
        outputs.append(valid & data)
        points.append(point)
        roots.append(root)
        states.append((valid, data))
        valid, data = en, root
    return outputs, points, roots, states


def main():
    checked = clauses = divergent = 0
    for trace in itertools.product(tuple(itertools.product((0, 1), repeat=2)), repeat=3):
        original = run(None, trace)[0]
        for failed in (0, 255, 37, 74, 111, 148, 185, 222):
            outputs, points, roots, states = run(failed, trace)
            if outputs == original:
                continue
            end = next(i for i, (a, b) in enumerate(zip(outputs, original)) if a != b)
            terms = set(zip(points[:end+1], (1-v for v in roots[:end+1])))
            assert all(((failed >> p) & 1) != value for p, value in terms)
            clauses += 1
            for candidate in range(256):
                out, _, _, new_states = run(candidate, trace)
                if out[:end+1] == original[:end+1]:
                    assert any(((candidate >> p) & 1) == value for p, value in terms)
                    divergent += new_states[:end+1] != states[:end+1]
                checked += 1
    result = dict(clauses=clauses, function_trace_checks=checked,
                  successful_distinct_trajectories=divergent, status='PASS')
    assert divergent > 0
    print(json.dumps(result, indent=2))
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
