#!/usr/bin/env python3
"""Focused proof scheduling, immutable-cache and actual-product tests."""
import json
import os
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

from anytime import (Budget, FrozenQueries, Graph, aggregate, prove_chunk,
                     publish_checkpoint, verify_checkpoint, file_identity)
from prototype import (Aiger, Config, Structure, compile_graph, recipe_eval,
                       sha, signatures, write_json)
from product import write_aig


def budget():
    start = time.monotonic()
    return Budget(start, start + 30)


def fixture(directory, same_next=True):
    # q1'=a, q2'=a: a*q1*b*q2 == a*q1*b on all reset-reachable states.
    path = directory / "input.aig"
    write_aig(path, dict(ni=2, nl=2, gates=[(2, 6), (4, 8), (10, 12)],
                        outputs=[14], latches=[2, 2 if same_next else 4]))
    a = Aiger(path)
    g, base, step, reset = compile_graph(a)
    (free, _, _), mask = signatures(g, [base, step, reset], Config(lanes=64))
    recipe, out = [10, 4], -2
    difference = recipe_eval(recipe, out, free, mask) ^ free[7]
    candidate = dict(root=7, recipe=recipe, out=out,
        witness_lane=(difference & -difference).bit_length() - 1,
        **Structure(a).cost(7, recipe, out))
    return path, a, g, dict(free=base, reset=reset, step=step), free, mask, candidate


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.directory = Path(self.tmp.name)
        g = Graph()
        g.pi()
        solver = self.directory / "unused_solver"
        solver.write_text("unused test solver")
        self.broker = FrozenQueries(g, self.directory, solver, budget())

    def tearDown(self):
        self.tmp.cleanup()

    def fake(self, outcomes):
        pending = iter(outcomes)
        def run(queries, phase):
            answers = [next(pending) for _ in queries]
            return answers, [dict(result={-1: "UNSAT", 0: "UNKNOWN", 1: "SAT"}[x],
                                  reused=False) for x in answers]
        return run

    def test_conclusive_identical_queries_reuse_only(self):
        with patch.object(self.broker, "_batch", side_effect=self.fake([-1, 1])) as mocked:
            answers, receipts = self.broker.solve([[0], [0], [2], [2]], "reset")
            self.assertEqual(answers, [-1, -1, 1, 1])
            self.assertEqual(mocked.call_count, 1)
            self.assertEqual(self.broker.metrics["conclusive_cache_hits"], 2)
            self.assertTrue(receipts[1]["reused"])
            self.assertTrue(receipts[3]["reused"])

    def test_unknown_is_requeried_not_broadcast(self):
        with patch.object(self.broker, "_batch", side_effect=self.fake([0, -1])) as mocked:
            answers, receipts = self.broker.solve([[0], [0], [0]], "reset")
            self.assertEqual(answers, [0, -1, -1])
            self.assertEqual(mocked.call_count, 2)
            self.assertEqual(self.broker.metrics["unknown_not_cached"], 1)
            self.assertFalse(receipts[0]["reused"])
            self.assertTrue(receipts[2]["reused"])

    def test_unknown_retries_on_later_phase_too(self):
        with patch.object(self.broker, "_batch", side_effect=self.fake([0, 1])) as mocked:
            self.assertEqual(self.broker.solve([[2]], "reset")[0], [0])
            self.assertEqual(self.broker.solve([[2]], "step")[0], [1])
            self.assertEqual(mocked.call_count, 2)

    def test_cache_hit_rejects_changed_cnf(self):
        with patch.object(self.broker, "_batch", side_effect=self.fake([-1])):
            self.broker.solve([[0]], "reset")
        self.broker.cnf.write_text("2 1\n1 0\n")
        with self.assertRaisesRegex(ValueError, "CNF changed"):
            self.broker.solve([[0]], "step")

    def test_solver_mutation_with_preserved_mtime_rejected_on_cache_hit(self):
        with patch.object(self.broker, "_batch", side_effect=self.fake([-1])):
            self.broker.solve([[0]], "reset")
        solver = self.broker.solver
        stat = solver.stat()
        solver.write_text("changed test solve")  # same length; restore original mtime
        os.utime(solver, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        self.assertEqual(solver.stat().st_size, stat.st_size)
        self.assertEqual(solver.stat().st_mtime_ns, stat.st_mtime_ns)
        with self.assertRaisesRegex(ValueError, "solver executable identity changed"):
            self.broker.solve([[0]], "step")

    def test_between_chunk_solver_replacement_rejected(self):
        expected = self.broker.solver_identity
        replacement = self.directory / "replacement"
        replacement.write_text("unused test solver")
        replacement.replace(self.broker.solver)
        graph = Graph()
        graph.pi()
        other = self.directory / "other"
        other.mkdir()
        with self.assertRaisesRegex(ValueError, "solver executable identity changed"):
            FrozenQueries(graph, other, self.broker.solver, budget(), expected)

    def test_exact_ordered_assumption_tuple(self):
        with patch.object(self.broker, "_batch", side_effect=self.fake([-1, -1])) as mocked:
            self.broker.solve([[0, 2], [2, 0]], "reset")
            self.assertEqual(len(mocked.call_args.args[0]), 2)
            self.assertEqual(self.broker.metrics["conclusive_cache_hits"], 0)

    def test_invalid_assumption_rejected(self):
        for query in ([], [4], [-1]):
            with self.assertRaises(ValueError):
                self.broker.solve([query], "reset")

    def test_partial_solver_result_never_admitted(self):
        solver = self.directory / "incomplete_solver.py"
        solver.write_text("#!/usr/bin/env python3\nimport pathlib,sys\npathlib.Path(sys.argv[3]).write_text('query,result,conflicts,wall_s\\n0,-1,0,0\\n')\n")
        solver.chmod(0o755)
        self.broker.solver = solver
        self.broker.solver_identity = file_identity(solver)
        with self.assertRaisesRegex(ValueError, "incomplete solver batch"):
            self.broker.solve([[0], [2]], "reset")
        self.assertFalse(self.broker.cache)

    def test_invalid_solver_status_never_admitted(self):
        solver = self.directory / "invalid_solver.py"
        solver.write_text("#!/usr/bin/env python3\nimport pathlib,sys\npathlib.Path(sys.argv[3]).write_text('query,result,conflicts,wall_s\\n0,2,0,0\\n')\n")
        solver.chmod(0o755)
        self.broker.solver = solver
        self.broker.solver_identity = file_identity(solver)
        with self.assertRaisesRegex(ValueError, "invalid solver status"):
            self.broker.solve([[0]], "reset")
        self.assertFalse(self.broker.cache)


@unittest.skipUnless(os.environ.get("STRAN2_SOLVER"), "requires STRAN2_SOLVER")
class ProofTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.directory = Path(self.tmp.name)
        self.solver = Path(os.environ["STRAN2_SOLVER"])

    def tearDown(self):
        self.tmp.cleanup()

    def test_full_relation_then_exact_checkpoint(self):
        path, a, g, mappings, free, _, candidate = fixture(self.directory)
        qualified, report = prove_chunk(a, g, mappings, free, [candidate],
            self.directory / "chunks" / "chunk_00000", self.solver, budget(), sha(path))
        self.assertEqual(len(qualified), 1)
        self.assertEqual(qualified[0]["proof"]["step"], "UNSAT")
        self.assertEqual(report["requested_queries"], 3)
        with patch("anytime.emit") as emitted:
            result = publish_checkpoint(path, qualified, self.directory, 0, budget(), sha(path),
                                        dict(searched_roots=1))
        notice = emitted.call_args.args[0]
        target, metadata = verify_checkpoint(self.directory, notice, sha(path))
        self.assertEqual(result["exact_same_selected_set_build_gain"], 1)
        self.assertEqual(result["selected_builds"], 1)
        self.assertEqual(metadata["product"]["product_and"], 2)
        self.assertIsNone(result["validated_standalone_noncomb_build_gain"])
        self.assertTrue((target / "selection.json").exists())

    def test_reset_sat_skips_free_and_step(self):
        path, a, g, mappings, free, mask, candidate = fixture(self.directory)
        candidate["out"] = -3
        difference = recipe_eval(candidate["recipe"], -3, free, mask) ^ free[7]
        candidate["witness_lane"] = (difference & -difference).bit_length() - 1
        qualified, report = prove_chunk(a, g, mappings, free, [candidate],
            self.directory / "chunks" / "chunk_00000", self.solver, budget(), sha(path))
        self.assertEqual(qualified, [])
        self.assertEqual(candidate["proof"]["reset"], "SAT")
        self.assertEqual(candidate["proof"]["free"], "NOT_RUN")
        self.assertEqual(candidate["proof"]["step"], "NOT_RUN")
        self.assertEqual(report["actual_queries"], 1)

    def test_step_sat_never_product_eligible(self):
        path, a, g, mappings, free, _, candidate = fixture(self.directory, same_next=False)
        qualified, report = prove_chunk(a, g, mappings, free, [candidate],
            self.directory / "chunks" / "chunk_00000", self.solver, budget(), sha(path))
        self.assertEqual(qualified, [])
        self.assertEqual(candidate["proof"]["free"], "SAT")
        self.assertEqual(candidate["proof"]["reset"], "UNSAT")
        self.assertEqual(candidate["proof"]["step"], "SAT")

    def test_unknown_reset_never_step_or_qualification(self):
        path, a, g, mappings, free, _, candidate = fixture(self.directory)
        with patch.object(FrozenQueries, "_batch", return_value=([0], [dict(result="UNKNOWN", reused=False)])):
            qualified, report = prove_chunk(a, g, mappings, free, [candidate],
                self.directory / "chunks" / "chunk_00000", self.solver, budget(), sha(path))
        self.assertEqual(qualified, [])
        self.assertEqual(candidate["proof"]["reset"], "UNKNOWN")
        self.assertEqual(candidate["proof"]["step"], "NOT_RUN")
        self.assertEqual(report["reset_unknown"], 1)

    def test_unproved_candidate_rejected_by_checkpoint(self):
        path, a, g, mappings, free, _, candidate = fixture(self.directory, same_next=False)
        prove_chunk(a, g, mappings, free, [candidate], self.directory / "chunks" / "chunk_00000", self.solver, budget(), sha(path))
        with patch("anytime.emit") as emitted, self.assertRaisesRegex(ValueError, "unproved candidate"):
            publish_checkpoint(path, [candidate], self.directory, 0, budget(), sha(path), {})
        emitted.assert_not_called()


class SummaryTests(unittest.TestCase):
    def test_partial_product_not_completed_search_or_missing_zero(self):
        rows = [dict(file="a", status="BUDGET_EXHAUSTED", search_complete=False, loaded_and=100,
                     product=dict(validated_standalone_noncomb_build_gain=2)),
                dict(file="b", status="BUDGET_EXHAUSTED", search_complete=False, loaded_and=100, product=None),
                dict(file="c", status="COMPLETE", search_complete=True, loaded_and=100,
                     product=dict(validated_standalone_noncomb_build_gain=None))]
        summary = aggregate(rows)
        self.assertEqual(summary["search_complete"], 1)
        self.assertEqual(summary["independently_validated"]["cases"], 1)
        self.assertEqual(summary["independently_validated"]["equal_case_percent"], 2)
        self.assertFalse(summary["missing_data_are_zero"])


if __name__ == "__main__":
    unittest.main()
