#!/usr/bin/env python3
"""Exhaustive original-transition checks and optional frozen-solver integration."""
import itertools
import os
from pathlib import Path
import random
import tempfile
import unittest

from deeper_image import compile_frames, load_runtime, make_queries, validate_candidate

# Explicit path is required while developed outside the checkout. After adding
# these files, use the saved pilot source, not whichever live source is on sys.path.
PACKAGE = os.environ.get("STRAN2_FROZEN_PACKAGE")
RUNTIME = load_runtime(PACKAGE) if PACKAGE else None


class Fixture:
    def __init__(self, ni, nl, gates, latches, outputs):
        self.ni, self.nl, self.gates = ni, nl, gates
        self.latches, self.outputs = latches, outputs
        self.initial = [0] * nl
        self.na, self.m = len(gates), ni + nl + len(gates)

    def step(self, inputs, state):
        assert len(inputs) == self.ni and len(state) == self.nl
        values = [0] + list(inputs) + list(state)
        def lit(x):
            return values[x // 2] ^ (x & 1)
        for x, y in self.gates:
            values.append(lit(x) & lit(y))
        return [lit(x) for x in self.outputs], [lit(x) for x in self.latches], values


def evaluate_graph(g, assignment):
    values = [0]
    for node, gate in enumerate(g.gates[1:], 1):
        if gate is None:
            values.append(assignment.get(2 * node, 0))
        else:
            x, y = gate
            values.append((values[x // 2] ^ (x & 1)) & (values[y // 2] ^ (y & 1)))
    return values


def exhaustive_answers(a, candidate, depth):
    """Enumerate each obligation directly in the original sequential fixture.

    Does not use compile_frames, Graph, CNF, or the formal recipe evaluator.
    """
    def recipe(values):
        gates = []
        def lit(code):
            if code >= 0:
                return values[code // 2] ^ (code & 1)
            index, phase = divmod(-code - 2, 2)
            return gates[index] ^ phase
        for i in range(0, len(candidate["recipe"]), 2):
            gates.append(lit(candidate["recipe"][i]) & lit(candidate["recipe"][i + 1]))
        return lit(candidate["out"])

    def exists_difference(frame, reset):
        states = [[0] * a.nl] if reset else itertools.product((0, 1), repeat=a.nl)
        for initial in states:
            for bits in itertools.product((0, 1), repeat=a.ni * (frame + 1)):
                state = list(initial)
                for t in range(frame + 1):
                    _, state, values = a.step(bits[t * a.ni:(t + 1) * a.ni], state)
                if values[candidate["root"]] != recipe(values):
                    return 1
        return -1
    return [exists_difference(frame, True) for frame in range(depth)] + [exists_difference(depth, False)]


@unittest.skipUnless(RUNTIME, "set STRAN2_FROZEN_PACKAGE to the explicit frozen source directory")
class ExhaustiveTests(unittest.TestCase):
    def check_frames(self, a, depth):
        g, reset, image = compile_frames(a, depth, RUNTIME.Graph)
        variables = [x for row in reset + image for x in row["pi"]] + image[0]["state"]
        self.assertEqual(len(variables), len(set(variables)))
        for frames, reset_branch in ((reset, True), (image, False)):
            count = len(frames)
            states = [[0] * a.nl] if reset_branch else itertools.product((0, 1), repeat=a.nl)
            for initial in states:
                for bits in itertools.product((0, 1), repeat=count * a.ni):
                    assignment = dict(zip(image[0]["state"], initial)) if not reset_branch else {}
                    for t, row in enumerate(frames):
                        assignment.update(zip(row["pi"], bits[t * a.ni:(t + 1) * a.ni]))
                    values = evaluate_graph(g, assignment)
                    state = list(initial)
                    for t, row in enumerate(frames):
                        _, state, original = a.step(bits[t * a.ni:(t + 1) * a.ni], state)
                        decoded = [values[lit // 2] ^ (lit & 1) for lit in row["mapping"]]
                        self.assertEqual(decoded, original, (t, reset_branch, bits, initial))

    def compiled_answers(self, a, c, depth):
        g, queries, _, frames = make_queries(a, [(0, c)], depth, RUNTIME)
        answers = []
        for query, branch in zip(queries, [frames["reset"]] * depth + [frames["unrestricted_image"]]):
            variables = [x for row in branch for x in row["pi"]]
            if branch is frames["unrestricted_image"]:
                variables += branch[0]["state"]
            answer = -1
            for bits in itertools.product((0, 1), repeat=len(variables)):
                values = evaluate_graph(g, dict(zip(variables, bits)))
                lit = query[0]
                if values[lit // 2] ^ (lit & 1):
                    answer = 1
                    break
            answers.append(answer)
        self.assertEqual(answers, exhaustive_answers(a, c, depth))
        return answers

    def test_delay_transient_invariant_needs_depth_two(self):
        a = Fixture(0, 2, [], [0, 2], [4])
        c = dict(root=2, recipe=[], out=0)
        self.assertEqual(self.compiled_answers(a, c, 1), [-1, 1])
        self.assertEqual(self.compiled_answers(a, c, 2), [-1, -1, -1])
        self.check_frames(a, 3)

    def test_self_loop_unreachable_state_remains_unproved(self):
        a = Fixture(0, 1, [], [2], [2])
        c = dict(root=1, recipe=[], out=0)
        self.assertEqual(self.compiled_answers(a, c, 1), [-1, 1])
        self.assertEqual(self.compiled_answers(a, c, 2), [-1, -1, 1])

    def test_intermediate_reset_frame_cannot_be_omitted(self):
        # q0'=1,q1'=q0; q0=q1 at reset and everywhere after two steps,
        # but the actual first reset successor is (1,0).
        a = Fixture(0, 2, [], [1, 2], [2, 4])
        c = dict(root=2, recipe=[], out=2)
        self.assertEqual(self.compiled_answers(a, c, 2), [-1, 1, -1])

    def test_current_pi_independent_from_predecessor(self):
        # q'=x,v'=1; q&v != current_x&v from the first active frame.
        a = Fixture(1, 2, [(4, 6)], [2, 1], [8])
        c = dict(root=4, recipe=[2, 6], out=-2)
        self.assertEqual(self.compiled_answers(a, c, 2), [-1, 1, 1])
        self.check_frames(a, 3)

    def test_all_predecessor_frame_pi_independent(self):
        # q0'=x,q1'=q0: image2 q1=x0 while q0=x1; tying old PI fails.
        a = Fixture(1, 2, [], [2, 4], [6])
        c = dict(root=3, recipe=[], out=4)
        self.assertEqual(self.compiled_answers(a, c, 2), [-1, 1, 1])
        self.check_frames(a, 3)

    def test_constants_complemented_next_state_and_internal_gates(self):
        a = Fixture(2, 2, [(3, 6), (5, 8), (10, 13)], [11, 1], [14, 9])
        self.check_frames(a, 3)
        c = dict(root=7, recipe=[2, 5, -3, 8], out=-5)
        self.compiled_answers(a, c, 2)

    def test_combinational_circuit_with_no_state(self):
        a = Fixture(2, 0, [(2, 4)], [], [6])
        self.check_frames(a, 3)
        self.assertEqual(self.compiled_answers(a, dict(root=3, recipe=[2, 4], out=-2), 2), [-1] * 3)
        self.assertEqual(self.compiled_answers(a, dict(root=3, recipe=[], out=0), 2), [1] * 3)

    def test_random_small_original_transition_exhaustion(self):
        rng = random.Random(10723)
        for trial in range(15):
            gates = [tuple(rng.randrange(2 * node) for _ in range(2)) for node in range(4, 7)]
            a = Fixture(1, 2, gates, [rng.randrange(14) for _ in range(2)], [12])
            self.check_frames(a, 3)
            c = dict(root=6, recipe=[rng.randrange(12), rng.randrange(12)], out=-3)
            self.compiled_answers(a, c, 2)

    def test_reject_bad_graph_and_recipe(self):
        a = Fixture(0, 1, [], [2], [2])
        for depth in (0, -1, 1.0, True):
            with self.assertRaises(ValueError):
                compile_frames(a, depth, RUNTIME.Graph)
        for c in (dict(root=1, recipe=[2, 0], out=-2), dict(root=1, recipe=[-2, 0], out=-2),
                  dict(root=1, recipe=[0], out=0), dict(root=1, recipe=[], out=-1)):
            with self.assertRaises(ValueError):
                validate_candidate(a, c)
        a.initial = [1]
        with self.assertRaises(ValueError):
            compile_frames(a, 2, RUNTIME.Graph)
        a.initial, a.latches = [0], [4]
        with self.assertRaises(ValueError):
            compile_frames(a, 2, RUNTIME.Graph)

    def test_deadline_checked_during_frame_construction(self):
        d = RUNTIME.Deadline(1)
        d.end = 0
        with self.assertRaises(TimeoutError):
            compile_frames(Fixture(0, 1, [], [2], [2]), 2, RUNTIME.Graph, d)


@unittest.skipUnless(RUNTIME and os.environ.get("STRAN2_SOLVER"), "set frozen source and STRAN2_SOLVER")
class SolverTests(unittest.TestCase):
    def test_solver_matches_exhaustive_obligations(self):
        fixtures = [
            (Fixture(0, 2, [], [0, 2], [4]), dict(root=2, recipe=[], out=0)),
            (Fixture(0, 1, [], [2], [2]), dict(root=1, recipe=[], out=0)),
            (Fixture(0, 2, [], [1, 2], [4]), dict(root=2, recipe=[], out=2)),
            (Fixture(1, 2, [(4, 6)], [2, 1], [8]), dict(root=4, recipe=[2, 6], out=-2)),
            (Fixture(1, 2, [], [2, 4], [6]), dict(root=3, recipe=[], out=4)),
        ]
        for a, c in fixtures:
            for depth in (1, 2, 3):
                g, queries, _, _ = make_queries(a, [(0, c)], depth, RUNTIME)
                with tempfile.TemporaryDirectory() as tmp:
                    answers, stats = RUNTIME.run_queries(g, queries, Path(tmp), Path(os.environ["STRAN2_SOLVER"]), RUNTIME.Deadline(10))
                self.assertEqual(answers, exhaustive_answers(a, c, depth))
                self.assertEqual(stats["conflicts_per_query"], 1000)


if __name__ == "__main__":
    unittest.main()
