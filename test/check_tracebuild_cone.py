#!/usr/bin/env python3
"""Independently check temporal CEX constraints over finite Boolean functions.

This checks a necessary-condition lemma, not bounded equivalence as a proof.
The final targeted counterexample also has a full reachable-product check.
"""
import collections
import itertools
import json


def trace(table, inputs, feedback):
    v = data = 0
    outputs, patterns, values = [], [], []
    for en, din in inputs:
        outputs.append(v & data)
        row = en | (din << 1) | ((data << 2) if feedback else 0)
        value = (table >> row) & 1
        patterns.append(row)
        values.append(value)
        v, data = en, value
    return outputs, patterns, values


def check():
    checked = naive_failures = failures = 0
    for feedback in (False, True):
        size = 1 << (3 if feedback else 2)
        source = sum((((row & 1) & ((row >> 1) & 1))) << row for row in range(size))
        for inputs in itertools.product(tuple(itertools.product((0, 1), repeat=2)), repeat=3):
            expected = trace(source, inputs, feedback)[0]
            for failed in (0, (1 << size) - 1,
                           sum(((row >> 1) & 1) << row for row in range(size))):
                outputs, patterns, values = trace(failed, inputs, feedback)
                bad = next((i for i, (a, b) in enumerate(zip(expected, outputs)) if a != b), None)
                if bad is None:
                    continue
                failures += 1
                assert bad > 0
                selected = range(bad) if feedback else (bad - 1,)
                for candidate in range(1 << size):
                    actual = trace(candidate, inputs, feedback)[0][bad]
                    agrees = all(((candidate >> patterns[t]) & 1) == values[t] for t in selected)
                    if agrees:
                        assert actual == outputs[bad]
                        checked += 1
                    naive_agrees = ((candidate >> patterns[bad - 1]) & 1) == values[bad - 1]
                    naive_failures += naive_agrees and actual != outputs[bad]
    assert checked and naive_failures

    # A genuinely equivalent candidate can use an invariant differently from
    # the failed recipe. Its extra XOR term vanishes on its own reachable
    # states but not on the failed recipe's v=0,data=1 state.
    def candidate(v, data, en, din):
        return (en & din) ^ (data & (1 - v))
    initial = (0, 0, 0, 0)
    queue = collections.deque([initial]); seen = {initial}
    while queue:
        va, da, vb, db = queue.popleft()
        assert va & da == vb & db
        for en, din in itertools.product((0, 1), repeat=2):
            nxt = (en, en & din, en, candidate(vb, db, en, din))
            if nxt not in seen:
                seen.add(nxt); queue.append(nxt)
    # Failed f=1, PI trace (0,0),(1,0),(0,0): first mismatch at cycle 2.
    assert candidate(0, 1, 1, 0) == 1  # matches f on its last relevant tuple
    assert candidate(0, 0, 0, 0) == 0  # earlier difference must stay in clause
    return {'failed_traces': failures, 'checked_matching_candidates': checked,
            'naive_last_frame_violations': naive_failures,
            'targeted_globally_equivalent_candidate_product_states': len(seen),
            'status': 'complete_pool_closure_PASS'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
