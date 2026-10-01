#!/usr/bin/env python3
"""Unit tests plus optional real-solver/ABC integration (environment variables)."""
import itertools
import json
import os
from pathlib import Path
import random
import tempfile
import unittest

from prototype import (Aiger, Config, Deadline, Structure, compile_graph, diagnose,
                       graph_recipe, invert, normalize, recipe_eval, run_queries, sha, signatures, search_root)
from product import rebuild, select, write_aig, create_product


class Fixture:
    def __init__(self, ni, nl, gates, latches, outputs):
        self.ni, self.nl, self.gates = ni, nl, gates
        self.latches, self.outputs = latches, outputs
        self.initial = [0] * nl
        self.na, self.no = len(gates), len(outputs)
        self.m = ni + nl + len(gates)

    def step(self, inputs, state):
        values = [0] + list(inputs) + list(state)
        def lit(code):
            return values[code // 2] ^ (code & 1)
        for x, y in self.gates:
            values.append(lit(x) & lit(y))
        return [lit(x) for x in self.outputs], [lit(x) for x in self.latches], values

    def graph(self):
        return dict(ni=self.ni, nl=self.nl, gates=self.gates,
                    latches=self.latches, outputs=self.outputs)


class UnitTests(unittest.TestCase):
    def test_packed_complement_and_references(self):
        self.assertEqual(invert(-2), -3)
        self.assertEqual(invert(-3), -2)
        for a, b, c in itertools.product((0, 1), repeat=3):
            values = [0, a, b, c]
            self.assertEqual(recipe_eval([2, 4, -3, 6], -5, values), 1 ^ ((1 ^ (a & b)) & c))
        with self.assertRaises(ValueError):
            recipe_eval([-2, 2], -2, [0, 1])
        with self.assertRaises(ValueError):
            recipe_eval([2, 2], -1, [0, 1])

    def test_retained_internal_divisor_cost(self):
        # d=ab; p=dc; r=pb. Keeping d must retain its entire cone.
        a = Fixture(3, 0, [(2, 4), (8, 6), (10, 4)], [], [12])
        s = Structure(a)
        cost = s.cost(6, [8, 6], -2)
        self.assertEqual(cost["original_mffc"], 3)
        self.assertEqual(cost["retained_mffc_nodes"], [4])
        self.assertEqual(cost["removable_nodes"], [5, 6])
        self.assertEqual(cost["conservative_gain"], 1)
        with self.assertRaises(ValueError):
            s.cost(6, [12, 2], -2)

    def test_retained_dependency_chain(self):
        a = Fixture(4, 0, [(2, 4), (10, 6), (12, 8), (14, 6)], [], [16])
        cost = Structure(a).cost(8, [12, 8], -2)
        self.assertEqual(cost["retained_mffc_nodes"], [5, 6])
        self.assertEqual(cost["removable"], 2)

    def test_hash_demotes_direct(self):
        a = Fixture(3, 0, [(2, 4), (8, 6)], [], [10])
        recipe, out = normalize(Structure(a), 5, [2, 4], -2)
        self.assertEqual((recipe, out), ([], 8))
        recipe, out = normalize(Structure(a), 5, [2, 4, -2, 6], -2)
        self.assertEqual((recipe, out), ([], 8))

    def test_no_dead_fresh_gates_and_normalization_truth(self):
        a = Fixture(3, 0, [(2, 4), (8, 6), (10, 2)], [], [12])
        s = Structure(a)
        recipe, out = normalize(s, 6, [2, 6, -3, 4, 2, 4], -5)
        self.assertEqual(len(recipe), 4)
        for vals in itertools.product((0, 1), repeat=3):
            original = a.step(vals, [])[2]
            self.assertEqual(recipe_eval(recipe, out, original),
                             recipe_eval([2, 6, -3, 4, 2, 4], -5, original))

    def test_binary_roundtrip_and_empty_replay(self):
        a = Fixture(2, 2, [(2, 4), (2, 6), (12, 4)], [2, 2], [10, 14])
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "roundtrip.aig"
            write_aig(path, rebuild(a, []))
            b = Aiger(path)
            for assignment in itertools.product((0, 1), repeat=4):
                self.assertEqual(a.step(assignment[:2], assignment[2:])[:2],
                                 b.step(assignment[:2], assignment[2:])[:2])

    def test_reject_unsupported_interfaces_and_reset(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "unsupported.aig"
            for data in (b"aig 1 0 1 1 0\n0 1\n2\n", b"aig 1 0 1 1 0\n0 2\n2\n",
                         b"aig 1 0 1 1 0 1\n0\n2\n", b"aig 2 0 1 1 0\n0\n2\n"):
                p.write_bytes(data)
                with self.assertRaises(ValueError):
                    Aiger(p)

    def test_conflicting_selected_dependencies(self):
        a = Fixture(3, 0, [(2, 4), (8, 6), (10, 4)], [], [12])
        s = Structure(a)
        c1 = dict(root=5, recipe=[2, 6], out=-2, **s.cost(5, [2, 6], -2))
        c2 = dict(root=6, recipe=[8, 6], out=-2, **s.cost(6, [8, 6], -2))
        chosen, rejected = select(s, [c1, c2])
        self.assertEqual(len(chosen), 1)
        self.assertEqual(len(rejected), 1)

    def test_raw_two_gate_template_can_cost_one_gate(self):
        a = Fixture(2, 2, [(2, 4), (2, 6), (12, 4)], [2, 2], [10, 14])
        s = Structure(a)
        g, base, step, reset = compile_graph(a)
        config = Config(lanes=32)
        (free, image, initial), mask = signatures(g, [base, step, reset], config)
        seq = [x | (y << config.lanes) for x, y in zip(image, initial)]
        seq_mask = (1 << (2 * config.lanes)) - 1
        # Nonlinear d=5 deliberately absent from the explicit pool. A raw first
        # AND hashes to it. Raw2 is legal with MFFC2 because normalized cost=1.
        args = (s, 7, [1, 2, 4], {}, seq, seq_mask, free, mask)
        old, _ = search_root(*args, Config(lanes=32, max_gates=1), Deadline(10))
        found, _ = search_root(*args, config, Deadline(10))
        self.assertEqual(old, [])
        self.assertTrue(any(5 in c["divisors"] and c["fresh_gates"] == 1 and
                            c["conservative_gain"] == 1 for c in found))

    def test_product_binds_input_hash_and_deadline(self):
        a = Fixture(2, 2, [(2, 4), (2, 6), (12, 4)], [2, 2], [10, 14])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "input.aig"
            write_aig(path, a.graph())
            with self.assertRaisesRegex(ValueError, "input changed"):
                create_product(path, [], root, expected_input_sha256="0" * 64)
            deadline = Deadline(10)
            deadline.end = 0
            with self.assertRaises(TimeoutError):
                create_product(path, [], root, deadline=deadline)

    def test_random_normalization_truth(self):
        rng = random.Random(624981)
        for _ in range(50):
            gates = [tuple(rng.randrange(2 * node) for _ in range(2)) for node in range(5, 15)]
            a = Fixture(4, 0, gates, [], [28])
            s = Structure(a)
            recipe = []
            for j in range(3):
                choices = list(range(2 * 14)) + [-i - 2 for i in range(2 * j)]
                recipe.extend(rng.choices(choices, k=2))
            recipe2, out = normalize(s, 14, recipe, -7)
            for bits in itertools.product((0, 1), repeat=4):
                values = a.step(bits, [])[2]
                self.assertEqual(recipe_eval(recipe, -7, values), recipe_eval(recipe2, out, values))


@unittest.skipUnless(os.environ.get("STRAN2_SOLVER"), "set STRAN2_SOLVER for real SAT tests")
class IntegrationTests(unittest.TestCase):
    def obligations(self, a, root, recipe, out):
        g, base, step, reset = compile_graph(a)
        queries = [[g.xor(mapping[root], graph_recipe(g, mapping, recipe, out))]
                   for mapping in (base, reset, step)]
        with tempfile.TemporaryDirectory() as tmp:
            answers, _ = run_queries(g, queries, Path(tmp), Path(os.environ["STRAN2_SOLVER"]), Deadline(10))
            return answers

    def test_reset_only_is_insufficient(self):
        a = Fixture(0, 1, [], [2], [2])
        self.assertEqual(self.obligations(a, 1, [], 0), [1, -1, 1])

    def test_image_only_is_insufficient(self):
        a = Fixture(0, 1, [], [1], [2])
        self.assertEqual(self.obligations(a, 1, [], 1), [1, 1, -1])

    def test_independent_current_pi(self):
        # q'=x, valid'=1; v&q&z differs from v&current_x&z.
        a = Fixture(2, 2, [(6, 8), (10, 4)], [2, 1], [12])
        self.assertEqual(self.obligations(a, 6, [8, 2, -2, 4], -4), [1, -1, 1])

    def test_valid_nonlinear_fixture_product(self):
        # d=x&y is shared; q0'=q1'=x. d&q1 replaces (x&q0)&y.
        a = Fixture(2, 2, [(2, 4), (2, 6), (12, 4)], [2, 2], [10, 14])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "input.aig"
            write_aig(path, a.graph())
            out = root / "run"
            out.mkdir()
            result = diagnose(dict(file="synthetic", input=str(path), input_sha256=sha(path), loaded_AND=3),
                              out, Path(os.environ["STRAN2_SOLVER"]), Config(),
                              Path(os.environ["STRAN2_ABC"]) if os.environ.get("STRAN2_ABC") else None)
            self.assertGreater(result["qualified_candidates"], 0)
            self.assertEqual(result["product"]["exact_same_selected_set_build_gain"], 1)
            self.assertEqual(result["product"]["selected_builds"], 1)
            if os.environ.get("STRAN2_ABC"):
                self.assertEqual(result["product"]["independent_dsec"]["status"], "PASS")
            chosen = json.loads((out / "selection.json").read_text())["selected"]
            self.assertTrue(any(d > 4 for c in chosen for d in c["divisors"]))
            b = Aiger(out / "product.aig")
            for trace in itertools.product(range(4), repeat=4):
                sa, sb = [0, 0], [0, 0]
                for pair in trace:
                    pi = [pair & 1, pair >> 1]
                    oa, sa, _ = a.step(pi, sa)
                    ob, sb, _ = b.step(pi, sb)
                    self.assertEqual(oa, ob)
                    self.assertEqual(sa, sb)


if __name__ == "__main__":
    unittest.main()
