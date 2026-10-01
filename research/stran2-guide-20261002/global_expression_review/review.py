#!/usr/bin/env python3
"""Independent, read-only whole-original structural-alias audit.

No imports from the candidate generator, product builder, or SAT infrastructure.
Reads frozen selection files and ordinary zero-reset binary AIGER inputs. The
hash includes every original gate, not just IDs smaller than a replacement root.
Only AND identities and structural hashing are used, not Boolean equivalence.
"""
import argparse
from collections import Counter, defaultdict, deque
import hashlib
import io
import json
from pathlib import Path
import random


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Aig:
    def __init__(self, path):
        f = io.BytesIO(Path(path).read_bytes())
        header = f.readline().decode().split()
        assert header[0] == 'aig' and len(header) >= 6, header
        self.m, self.ni, self.nl, no, na = map(int, header[1:6])
        assert all(int(x) == 0 for x in header[6:]), 'typed AIGER unsupported'
        self.nci = self.ni + self.nl
        assert self.m == self.nci + na
        self.latches = []
        for _ in range(self.nl):
            fields = list(map(int, f.readline().split()))
            assert len(fields) in (1, 2) and (len(fields) == 1 or fields[1] == 0)
            self.latches.append(fields[0])
        self.outputs = [int(f.readline()) for _ in range(no)]

        def varint():
            value = shift = 0
            while True:
                byte = f.read(1)
                assert byte, 'truncated varint'
                byte = byte[0]
                value |= (byte & 127) << shift
                if byte < 128:
                    return value
                shift += 7

        self.gates = [None] * (self.nci + 1)
        for node in range(self.nci + 1, self.m + 1):
            hi = node * 2 - varint()
            lo = hi - varint()
            assert 0 <= lo <= hi < node * 2
            self.gates.append((hi, lo))
        assert all(0 <= lit <= self.m * 2 + 1 for lit in self.latches + self.outputs)

    def tfi(self, node):
        seen, todo = set(), [node]
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            if n > self.nci:
                todo.extend(lit // 2 for lit in self.gates[n])
        return seen


def fold(x, y):
    if x == 0 or y == 0 or x == (y ^ 1):
        return 0
    if x == 1 or x == y:
        return y
    if y == 1:
        return x
    return None


class OriginalHash:
    def __init__(self, aig):
        self.a = aig
        self.hash = {}
        self.mapping = list(range(0, 2 * aig.nci + 1, 2))
        self.aliases = defaultdict(list)
        for node in range(aig.nci + 1):
            self.aliases[2 * node].append(2 * node)
        for node in range(aig.nci + 1, aig.m + 1):
            x, y = (self.mapping[lit // 2] ^ (lit & 1) for lit in aig.gates[node])
            value = fold(x, y)
            if value is None:
                value = self.hash.setdefault(tuple(sorted((x, y))), 2 * node)
            self.mapping.append(value)
            self.aliases[value].append(2 * node)

    def original_aliases(self, value):
        return sorted(self.aliases.get(value, []) +
                      [lit ^ 1 for lit in self.aliases.get(value ^ 1, [])])

    def recipe(self, recipe, out):
        assert len(recipe) % 2 == 0
        built, fresh, local_hash = [], {}, {}

        def source(code):
            if code >= 0:
                assert code // 2 <= self.a.m
                return self.mapping[code // 2] ^ (code & 1)
            assert code <= -2
            index, phase = divmod(-code - 2, 2)
            assert index < len(built), 'non-topological recipe'
            return built[index] ^ phase

        for i in range(0, len(recipe), 2):
            x, y = source(recipe[i]), source(recipe[i + 1])
            value = fold(x, y)
            if value is None:
                key = tuple(sorted((x, y)))
                value = self.hash.get(key, local_hash.get(key))
                if value is None:
                    value = 2 * (self.a.m + 1 + len(fresh))
                    local_hash[key] = value
                    fresh[value // 2] = key
            built.append(value)
        value = source(out)
        live, todo = set(), [value // 2]
        while todo:
            node = todo.pop()
            if node not in fresh or node in live:
                continue
            live.add(node)
            todo.extend(lit // 2 for lit in fresh[node])
        return value, built, fresh, live


def eval_aig(a, inputs, mask):
    values = [0] + list(inputs)
    assert len(values) == a.nci + 1
    for x, y in a.gates[a.nci + 1:]:
        values.append((values[x // 2] ^ (mask if x & 1 else 0)) &
                      (values[y // 2] ^ (mask if y & 1 else 0)))
    return values


def eval_recipe(recipe, out, values, mask):
    built = []

    def get(code):
        if code >= 0:
            return values[code // 2] ^ (mask if code & 1 else 0)
        index, phase = divmod(-code - 2, 2)
        return built[index] ^ (mask if phase else 0)

    for i in range(0, len(recipe), 2):
        built.append(get(recipe[i]) & get(recipe[i + 1]))
    return get(out)


def acyclic(a, dependencies):
    """Check all original nodes with designated root edges replaced, no builder."""
    pending, users = {}, defaultdict(list)
    for node in range(1, a.m + 1):
        deps = set(dependencies.get(node, [lit // 2 for lit in a.gates[node]]
                                    if node > a.nci else [])) - {0}
        pending[node] = len(deps)
        for dep in deps:
            users[dep].append(node)
    ready = deque(node for node, count in pending.items() if count == 0)
    while ready:
        node = ready.popleft()
        for user in users[node]:
            pending[user] -= 1
            if pending[user] == 0:
                ready.append(user)
    return sorted(node for node, count in pending.items() if count)


def audit_selection(a, candidates):
    h = OriginalHash(a)
    rng = random.Random(2026100101)
    mask = (1 << 128) - 1
    values = eval_aig(a, [rng.getrandbits(128) for _ in range(a.nci)], mask)
    assert all(values[node] == (values[lit // 2] ^ (mask if lit & 1 else 0))
               for node, lit in enumerate(h.mapping))
    rows, dependencies = [], {}
    for c in candidates:
        root, recipe, out = c['root'], c['recipe'], c['out']
        external = sorted({code // 2 for code in recipe + [out] if code >= 2})
        assert all(d < root for d in external), 'saved recipe violates prefix safety'
        value, built, fresh, live = h.recipe(recipe, out)
        aliases = h.original_aliases(value)
        alias_checks = [dict(literal=lit, source_node=lit // 2,
                             source_id_later_than_root=lit // 2 > root,
                             original_tfi_excludes_root=root not in a.tfi(lit // 2))
                        for lit in aliases]
        safe = [x['literal'] for x in alias_checks if x['original_tfi_excludes_root']]
        if aliases:
            category = 'output_alias_existing_original'
            assert safe, 'output has only cyclic raw-original aliases'
            dependencies[root] = [safe[0] // 2]
        else:
            dependencies[root] = external
            category = 'structurally_novel_output_entirely_new_gates'
        # Only recipe gates relevant to the final output are intermediates.
        # An original alias can be the fanin boundary of a fresh live gate.
        used_original = {lit // 2 for node in live for lit in fresh[node]
                         if lit // 2 <= a.m}
        intermediate = []
        for index, lit in enumerate(built):
            if lit // 2 not in used_original:
                continue
            matches = h.original_aliases(lit)
            later = [x for x in matches if x // 2 > root]
            if later:
                checks = [dict(literal=x, original_tfi_excludes_root=root not in a.tfi(x // 2))
                          for x in later]
                intermediate.append(dict(recipe_gate=index, canonical_literal=lit,
                                         later_original_aliases=checks))
        if not aliases and intermediate:
            category = 'structurally_novel_output_later_original_intermediate'
        if category == 'structurally_novel_output_entirely_new_gates':
            # Saved recipes were already prefix-normalized. Fail rather than
            # silently labeling a folded/dead/earlier-alias gate entirely new.
            assert len(live) == len(recipe) // 2
        # Evaluate independently to check phase, folding, and local references.
        extended = list(values)
        for node in sorted(fresh):
            assert node == len(extended)
            x, y = fresh[node]
            extended.append((extended[x // 2] ^ (mask if x & 1 else 0)) &
                            (extended[y // 2] ^ (mask if y & 1 else 0)))
        observed = extended[value // 2] ^ (mask if value & 1 else 0)
        assert observed == eval_recipe(recipe, out, values, mask)
        rows.append(dict(root=root, recipe=recipe, out=out, category=category,
                         output_canonical_literal=value, output_aliases=alias_checks,
                         later_original_intermediates=intermediate,
                         live_globally_new_gate_count=len(live),
                         original_prefix_divisors=external,
                         original_prefix_divisor_max=max(external, default=0),
                         structural_and_phase_simulation_128_assignments=True))
    residual = acyclic(a, dependencies)
    assert not residual, f'combined aliases are cyclic: {residual[:20]}'
    return dict(counts=dict(Counter(row['category'] for row in rows)),
                selected=len(rows), combined_raw_alias_dependency_graph_acyclic=True,
                original_hash_normalization_changed_nodes=sum(lit != 2 * n for n, lit in enumerate(h.mapping)),
                rows=rows)


def selftest():
    # IDs 1/2/3 are inputs; root 4 precedes existing 5=(1&2),
    # 6=(~5&3), and 7 duplicates 5 with reversed fanins.
    a = Aig.__new__(Aig)
    a.nci, a.ni, a.nl, a.m = 3, 3, 0, 7
    a.gates = [None] * 4 + [(2, 6), (2, 4), (11, 6), (4, 2)]
    h = OriginalHash(a)
    fixtures = [([2, 4], -2, 10), ([2, 4], -3, 11),
                ([2, 4, -3, 6], -2, 10),  # dead second gate
                ([2, 4, -3, 6], -4, 12),
                ([2, 4, -2, -3], -4, 0),
                ([2, 4, -2, -2], -5, 11),
                ([2, 4, 1, -2], -4, 10),
                ([2, 4, 0, -2], -4, 0)]
    for recipe, out, expected in fixtures:
        value, built, fresh, live = h.recipe(recipe, out)
        assert value == expected and not live
        for assignment in range(8):
            values = eval_aig(a, [(assignment >> i) & 1 for i in range(3)], 1)
            assert eval_recipe(recipe, out, values, 1) == (values[value // 2] ^ (value & 1))
    assert h.original_aliases(11) == [11, 15]
    r = audit_selection(a, [dict(root=4, recipe=[2, 4, -2, 7], out=-4)])
    assert r['rows'][0]['category'] == 'structurally_novel_output_later_original_intermediate'
    assert r['rows'][0]['live_globally_new_gate_count'] == 1
    assert acyclic(a, {4: [5]}) == []
    assert acyclic(a, {4: [5], 5: [4]})
    # Later source IDs can be cyclic: an explicit dependency test is required.
    a.gates[7] = (8, 2)
    assert 4 in a.tfi(7)
    assert acyclic(a, {4: [7]})
    return dict(status='PASS', normalization_fixtures=len(fixtures),
                exhaustive_assignments_per_fixture=8,
                later_intermediate_and_individual_combined_cycle_checks=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runs', nargs='+', default=['/tmp/image-guided-pilot-v1', '/tmp/nonlinear-anytime-pilot-v2'])
    parser.add_argument('--input-dir', type=Path, default=Path(__file__).resolve().parents[1] / 'inputs/first_seq')
    parser.add_argument('--out', type=Path, default=Path(__file__).with_name('review.json'))
    args = parser.parse_args()
    report = dict(schema=1, script_sha256=digest(__file__), selftest=selftest(),
                  classification='whole-original normalized structural hash, not Boolean equivalence or global sequential Direct saturation',
                  independent_parser_and_normalizer=True, sat_queries_run=0, product_replays_run=0, runs={})
    for run in args.runs:
        cases = {}
        for source in sorted(Path(run).glob('*/result.json')):
            result = json.loads(source.read_text())
            checkpoint = Path(result['selected_checkpoint']['directory'])
            selection = checkpoint / 'selection.json'
            candidates = json.loads(selection.read_text())['selected']
            input_path = args.input_dir / result['file']
            assert digest(input_path) == result['input_sha256']
            reviewed = audit_selection(Aig(input_path), candidates)
            reviewed.update(input_path=str(input_path), input_sha256=digest(input_path),
                            selection_path=str(selection), selection_sha256=digest(selection),
                            historical_product_and=result['product']['product_and'],
                            historical_product_reduction=result['product']['exact_same_selected_set_build_gain'])
            cases[source.parent.name] = reviewed
        totals = Counter()
        for case in cases.values():
            totals.update(case['counts'])
        report['runs'][run] = dict(total_selected=sum(c['selected'] for c in cases.values()),
                                  counts=dict(totals), cases=cases)
    report['accounting_assessment'] = {
        'verdict': 'Legitimate to retain the identical demoted recipe materialization in the same-selected-set no-genuine-Build replay.',
        'reason': 'Novelty is classified against the immutable original whole graph; replay mechanism can materialize its identical earlier-fanin expression at the replacement root. This is an existing-expression/Direct realization, not globally new Build, even when it allocates a temporary prefix node.',
        'exact_metric': 'AND count after cleanup of the identical selected set with globally structurally novel Build entries removed, minus AND count after cleanup of the full identical selected set. Preserve all Direct and demoted entries, and do not reselect.',
        'safety': 'Keep the original recipe prefix restriction and existing proof-backed builder. An original alias ID greater than the root is not itself a cycle, but raw reuse requires root-excluding TFI plus combined replacement dependency validation; never feed a future ID to an earlier-ID-only mapping array.',
        'limits': 'No new exact marginal or DSEC result is asserted here. Whole-original structural absence does not rule out Boolean-equivalent original nodes, sequential Direct alternatives, or native candidate-generator overlap.'}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({run: {'total_selected': r['total_selected'], 'counts': r['counts'],
                            'cases': {name: c['counts'] for name, c in r['cases'].items()}}
                      for run, r in report['runs'].items()}, indent=2))


if __name__ == '__main__':
    main()
