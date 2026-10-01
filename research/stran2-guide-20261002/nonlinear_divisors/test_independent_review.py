#!/usr/bin/env python3
"""Independent deterministic adversarial checks; no solver or ABC required.

The randomized pass uses seed 741902, 200 live DAGs, 100 recipes/DAG, and
exhaustive four-CI truth tables. It checks semantics and deletion accounting,
not sequential proof completeness or benchmark quality.
"""
from pathlib import Path
import random
import itertools
import sys
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import prototype as p
import product

SEED = 741902
GRAPHS = 200
RECIPES_PER_GRAPH = 100


def literal(values, code, mask):
    return values[code // 2] ^ (mask if code & 1 else 0)


def reference_recipe(recipe, out, values, mask):
    fresh = []

    def value(code):
        if code >= 0:
            return literal(values, code, mask)
        return fresh[(-code - 2) // 2] ^ (mask if (-code - 2) % 2 else 0)

    for first, second in zip(recipe[::2], recipe[1::2]):
        fresh.append(value(first) & value(second))
    return value(out)


def sink_live(a, replacement_root=None, used=()):
    todo = [code // 2 for code in a.outputs + a.latches]
    seen = set()
    while todo:
        node = todo.pop()
        if node in seen:
            continue
        seen.add(node)
        if node == replacement_root:
            todo.extend(used)
        elif node > a.ni + a.nl:
            todo.extend(code // 2 for code in a.gates[node - a.ni - a.nl - 1])
    return seen


class IndependentReview(unittest.TestCase):
    def test_unknown_or_sat_relation_never_enters_product(self):
        graph = dict(ni=2, nl=2, gates=[(2, 4), (2, 6), (12, 4)],
                     latches=[2, 2], outputs=[10, 14])
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            path = root / 'input.aig'
            product.write_aig(path, graph)
            for index, statuses in enumerate(((1, 0, -1), (1, -1, 0),
                                              (0, -1, -1), (1, 1, -1), (1, -1, 1))):
                out = root / str(index)
                out.mkdir()

                def synthetic_answers(_graph, queries, *_args):
                    self.assertEqual(len(queries) % 3, 0)
                    return list(statuses) * (len(queries) // 3), {'synthetic_status_test': True}

                with self.subTest(statuses=statuses), mock.patch.object(
                        p, 'run_queries', side_effect=synthetic_answers):
                    result = p.diagnose(
                        dict(file='synthetic-status-test', input=str(path),
                             input_sha256=p.sha(path), loaded_AND=3),
                        out, Path(__file__), p.Config())
                    self.assertGreater(result['candidate_count'], 0)
                    self.assertEqual(result['qualified_candidates'], 0)
                    self.assertEqual(result['product']['selected_builds'], 0)
                    self.assertIsNone(result['product']['validated_standalone_noncomb_build_gain'])

    def test_product_import_is_order_independent(self):
        result = subprocess.run(
            [sys.executable, '-B', '-c',
             'import sys; sys.path.insert(0, sys.argv[1]); import product',
             str(Path(__file__).resolve().parent)],
            capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_rebuild_and_binary_serialization(self):
        rng = random.Random(SEED + 1)
        with tempfile.TemporaryDirectory() as temp:
            for _ in range(50):
                nci, ngates = 4, 12
                a = SimpleNamespace(ni=2, nl=2, m=nci + ngates, na=ngates,
                                    gates=[], outputs=[32, 27], latches=[17, 24])
                for node in range(nci + 1, a.m + 1):
                    a.gates.append((rng.randrange(2 * node), rng.randrange(2 * node)))
                selected = []
                for root in sorted(rng.sample(range(nci + 1, a.m + 1), 4)):
                    selected.append(dict(root=root,
                                         recipe=[rng.randrange(2 * root), rng.randrange(2 * root),
                                                 -2 - rng.randrange(2), rng.randrange(2 * root)],
                                         out=-4 - rng.randrange(2)))
                by_root = {candidate['root']: candidate for candidate in selected}
                rebuilt = product.rebuild(a, selected)
                path = Path(temp) / 'rebuilt.aig'
                product.write_aig(path, rebuilt)
                parsed = p.Aiger(path)
                self.assertEqual((parsed.ni, parsed.nl, parsed.no), (2, 2, 2))
                self.assertEqual(parsed.initial, [0, 0])
                for world in itertools.product((0, 1), repeat=nci):
                    values = [0] + list(world)
                    for root, (first, second) in enumerate(a.gates, nci + 1):
                        if root in by_root:
                            candidate = by_root[root]
                            value = reference_recipe(candidate['recipe'], candidate['out'], values, 1)
                        else:
                            value = literal(values, first, 1) & literal(values, second, 1)
                        values.append(value)
                    expected = ([literal(values, code, 1) for code in a.outputs],
                                [literal(values, code, 1) for code in a.latches])
                    actual = parsed.step(list(world[:2]), list(world[2:]))[:2]
                    self.assertEqual(actual, expected)

    def test_dsec_parser_requires_clean_single_verdict(self):
        cases = [
            ('Networks are equivalent.', 'pass'),
            ('Networks are equivalent.\nNetworks are NOT EQUIVALENT.', 'parser-error'),
            ('Networks have different number of primary inputs\nNetworks are equivalent.',
             'interface-error'),
            ('Cannot open a file\nNetworks are equivalent.', 'checker-error'),
            ('usage: dsec\nNetworks are equivalent.', 'checker-error'),
            ('Networks are UNDECIDED.', 'undecided'),
            ('', 'parser-error'),
        ]
        for text, expected in cases:
            with self.subTest(text=text):
                self.assertEqual(product.dsec_answer({'status': 'exit'}, text), expected)
        for status in ('assertion', 'timeout', 'error'):
            self.assertEqual(product.dsec_answer({'status': status}, 'Networks are equivalent.'), status)

    def test_normalization_and_retention_exhaustively(self):
        rng = random.Random(SEED)
        checks = 0
        for graph_index in range(GRAPHS):
            nci, ngates = 4, rng.randint(4, 16)
            mask = (1 << (1 << nci)) - 1
            a = SimpleNamespace(ni=2, nl=2, m=nci + ngates, na=ngates,
                                gates=[], outputs=[2 * (nci + ngates)],
                                latches=[rng.randrange(2 * (nci + ngates + 1)) for _ in range(2)])
            # Chaining the previous gate makes every original AND live.
            for node in range(nci + 1, a.m + 1):
                a.gates.append((2 * (node - 1) + rng.randrange(2), rng.randrange(2 * node)))
            s = p.Structure(a)
            values = [0] + [sum(((world >> j) & 1) << world for world in range(1 << nci))
                            for j in range(nci)]
            for first, second in a.gates:
                values.append(literal(values, first, mask) & literal(values, second, mask))
            self.assertTrue(all(node in sink_live(a) for node in range(nci + 1, a.m + 1)))
            for _ in range(RECIPES_PER_GRAPH):
                root = rng.randrange(nci + 1, a.m + 1)
                recipe = []
                for gate in range(rng.randrange(1, 5)):
                    options = list(range(2 * root)) + [-x - 2 for x in range(2 * gate)]
                    recipe.extend([rng.choice(options), rng.choice(options)])
                options = list(range(2 * root)) + [-x - 2 for x in range(len(recipe))]
                out = rng.choice(options)
                normalized, new_out = p.normalize(s, root, recipe, out)
                expected = reference_recipe(recipe, out, values, mask)
                self.assertEqual(expected, reference_recipe(normalized, new_out, values, mask),
                                 (graph_index, root, recipe, out, normalized, new_out))
                self.assertEqual(expected, p.recipe_eval(normalized, new_out, values, mask))
                cost = s.cost(root, normalized, new_out)
                used = p.external_nodes(normalized, new_out)
                # sink_live keeps root as a virtual replacement marker. Its old
                # AND is deleted even though the virtual signal remains live.
                exact = {n for n in sink_live(a) - sink_live(a, root, used) if n > nci} | {root}
                self.assertEqual(set(cost['removable_nodes']), exact,
                                 (graph_index, root, normalized, new_out))
                checks += 1
        self.assertEqual(checks, GRAPHS * RECIPES_PER_GRAPH)

    def test_malformed_and_cyclic_references_fail_closed(self):
        a = SimpleNamespace(ni=1, nl=1, m=4, na=2, gates=[(2, 4), (2, 6)],
                            latches=[0], outputs=[8])
        s = p.Structure(a)
        for recipe, out in (([2], -2), ([-1, 2], -2), ([-2, 2], -2),
                            ([8, 2], -2), ([10, 2], -2)):
            with self.subTest(recipe=recipe, out=out):
                with self.assertRaises(ValueError):
                    p.normalize(s, 4, recipe, out)
        for code in (0, 1, 2, 3, -2, -3, -4, -5):
            self.assertEqual(p.invert(p.invert(code)), code)
        self.assertEqual(p.invert(-2), -3)

    def test_dead_created_intermediate_is_not_build(self):
        # q'=0; n4=a&~a; n5=a&q; n6=b&n5; root=n6&~n4.
        # Replacement (~a&b)&n4 is identically zero. The real root is zero
        # from reset but differs for free a=b=q=1. During reconstruction the
        # first recipe gate is created, then dies because its output folds to
        # zero. It must be demoted to Direct, never attributed to Build.
        graph = dict(ni=2, nl=1, latches=[0], outputs=[14],
                     gates=[(2, 3), (2, 6), (4, 10), (12, 9)])
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            product.write_aig(out / 'input.aig', graph)
            a = p.Aiger(out / 'input.aig')
            s = p.Structure(a)
            candidate = dict(root=7, recipe=[3, 4, -2, 8], out=-4)
            candidate.update(s.cost(7, candidate['recipe'], candidate['out']))
            self.assertGreater(candidate['conservative_gain'], 0)
            _, _, values = a.step([1, 1], [1])
            self.assertEqual(values[7], 1)
            self.assertEqual(reference_recipe(candidate['recipe'], candidate['out'], values, 1), 0)
            for pi in ([0, 0], [0, 1], [1, 0], [1, 1]):
                _, next_state, values = a.step(pi, [0])
                self.assertEqual(next_state, [0])
                self.assertEqual(values[7], 0)
            # The property above proves reset and unrestricted image equality;
            # this unit tests product classification independently of a solver.
            candidate.update(qualified_offline_opportunity=True,
                             proof=dict(free='SAT', reset='UNSAT', step='UNSAT',
                                        free_witness_replayed=True))
            result = product.create_product(out / 'input.aig', [candidate], out)
            self.assertEqual(result['selected_builds'], 0)
            self.assertEqual(result['exact_same_selected_set_build_gain'], 0)


if __name__ == '__main__':
    unittest.main()
