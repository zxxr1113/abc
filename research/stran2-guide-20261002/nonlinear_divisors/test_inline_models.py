#!/usr/bin/env python3
"""Receipt, model, frame, cache and original-transition replay adversaries."""
import copy
import csv
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from anytime import bind_executable, prove_chunk
import inline_models as im
import prototype as p
from product import write_aig
from test_anytime import budget, fixture

SOLVER = os.environ.get("STRAN2_INLINE_SOLVER")


@unittest.skipUnless(SOLVER, "requires STRAN2_INLINE_SOLVER")
class InlineModelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.solver = Path(SOLVER)
        cls.solver_identity, cls.solver_sha = bind_executable(cls.solver)

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.out = Path(self.tmp.name)
        self.path, self.a, self.g, self.maps, self.free, self.mask, self.c = fixture(self.out, same_next=False)
        self.context = dict(input_sha256=p.sha(self.path), source_hashes={"test": "f"*64},
                            solver_sha256=self.solver_sha)
        self.job = dict(case=dict(input=str(self.path), input_sha256=p.sha(self.path)),
                        out=str(self.out), solver_sha256=self.solver_sha, source_hashes=self.context["source_hashes"])

    def tearDown(self):
        self.tmp.cleanup()

    def broker(self):
        directory = self.out / "broker"
        directory.mkdir()
        p.write_json(directory / "candidates.unproved.json", [])
        p.write_json(directory / "query_literals.json", [])
        g = p.Graph()
        g.pi(); g.pi()
        return im.InlineFrozenQueries(g, directory, self.solver, budget(), self.solver_identity,
            context=dict(self.context, roles=dict(previous_inputs=[2], previous_state=[], current_inputs=[4]),
                         variables=[1, 2]))

    def prove(self, candidates=None):
        candidates = [self.c] if candidates is None else candidates
        qualified, report = prove_chunk(self.a, self.g, self.maps, self.free, candidates,
            self.out / "chunks" / "chunk_00000", self.solver, budget(), p.sha(self.path),
            self.solver_identity, inline_model_context=self.context)
        return candidates, qualified, report

    def collect(self, candidates, tag="replay"):
        return im.collect_inline_models(self.a, self.g, self.maps["free"], self.maps["step"],
            candidates, self.out / tag, self.job, budget(), {})

    def test_original_step_model_replays_without_any_new_solver_call(self):
        candidates, qualified, report = self.prove()
        self.assertFalse(qualified)
        self.assertEqual(report["actual_queries"], 3)
        self.assertEqual(report["inline_models_emitted"], 1)
        self.assertEqual(report["step_sat_model_available_requests"], 1)
        self.assertEqual(report["additional_model_solver_queries"], 0)
        with patch.object(im.subprocess, "run", side_effect=AssertionError("duplicate solve")):
            samples, replay = self.collect(candidates)
        self.assertEqual((len(samples), replay["models"], replay["queries"]), (1, 1, 0))
        row = json.loads((self.out / "replay/replayed_models.json").read_text())[0]
        self.assertFalse(row["reachable_teacher"])
        self.assertEqual(row["successor_state"], self.a.step(row["previous_inputs"], row["previous_state"])[1])
        self.assertNotEqual(row["root_value"], row["recipe_value"])
        self.assertEqual(len(list((self.out / "chunks/chunk_00000").glob("*.models.jsonl"))), 1)

    def test_guidance_accounting_identifies_original_query_source(self):
        candidates, _, _ = self.prove()
        job = dict(self.job, inline_image_models=True)
        guidance = im.InlineImageGuidance(self.a, self.g, self.maps["free"], self.maps["step"],
            [0]*(self.a.m+1), 1, self.free, self.mask, p.Structure(self.a), p.Config(), job, budget(), None)
        roots = [dict(root=7, pool=[1, 2, 3, 4, 5, 6], pool_info={})]
        guidance.remember_search(7, roots[0]["pool"], {}, [], {})
        guidance.mark_attempted(candidates)
        with patch.object(im.p, "search_root", return_value=([], {})), \
             patch.object(im.subprocess, "run", side_effect=AssertionError("duplicate solve")):
            guidance.refine(roots, candidates, self.out)
        report = json.loads((self.out / "image_guidance/round_00000/refinement.json").read_text())
        self.assertTrue(report["ordinary_proofs_reused_as_model_proofs"])
        self.assertEqual(report["model_source"], "original ordinary step-SAT receipt and projected model")
        self.assertEqual(report["additional_model_solver_queries"], 0)
        self.assertEqual(report["model_report"]["queries"], 0)
        self.assertEqual(report["model_report"]["models"], 1)
        self.assertEqual(guidance.report()["model_queries"], 0)

    def test_model_miss_only_round_never_claims_model_reuse(self):
        candidates, _, _ = self.prove()
        del candidates[0]["anytime_certificate"]["receipts"]["step"]["inline_image_model"]
        job = dict(self.job, inline_image_models=True)
        guidance = im.InlineImageGuidance(self.a, self.g, self.maps["free"], self.maps["step"],
            [0]*(self.a.m+1), 1, self.free, self.mask, p.Structure(self.a), p.Config(), job, budget(), None)
        roots = [dict(root=7, pool=[1, 2, 3, 4, 5, 6], pool_info={})]
        guidance.remember_search(7, roots[0]["pool"], {}, [], {})
        guidance.mark_attempted(candidates)
        with patch.object(im.subprocess, "run", side_effect=AssertionError("duplicate solve")):
            self.assertEqual(guidance.refine(roots, candidates, self.out), [])
        report = json.loads((self.out / "image_guidance/round_00000/refinement.json").read_text())
        self.assertFalse(report["ordinary_proofs_reused_as_model_proofs"])
        self.assertEqual(report["additional_model_solver_queries"], 0)
        self.assertEqual(report["model_report"]["models"], 0)
        self.assertEqual(report["model_report"]["model_cache_misses"], 1)
        self.assertEqual(guidance.report()["accepted_image_samples"], 0)

    def test_step_duplicates_share_one_model_but_replay_each_candidate(self):
        other = dict(self.c, recipe=list(reversed(self.c["recipe"])))
        candidates, _, report = self.prove([self.c, other])
        self.assertEqual(report["inline_models_emitted"], 1)
        self.assertEqual(report["step_sat_model_available_requests"], 2)
        self.assertTrue(other["anytime_certificate"]["receipts"]["step"]["reused"])
        with patch.object(im.d, "replay_model", wraps=im.d.replay_model) as replay:
            _, result = self.collect(candidates)
        self.assertEqual(replay.call_count, 2)
        self.assertEqual(result["models"], 2)
        self.assertEqual(result["raw_models_emitted"], 1)

    def test_cross_phase_sat_cache_is_explicit_model_miss_without_resolve(self):
        broker = self.broker()
        broker.solve([[2]], "free")
        with patch.object(im.subprocess, "run", side_effect=AssertionError("duplicate solve")):
            answers, receipts = broker.solve([[2]], "step")
        self.assertEqual(answers, [1])
        self.assertNotIn("inline_image_model", receipts[0])
        self.assertEqual(broker.metrics["step_sat_model_cache_misses"], 1)
        self.assertEqual(broker.metrics["actual_queries"], 1)
        self.assertFalse(list(broker.out.glob("*.models.jsonl")))

    def test_real_self_loop_free_to_step_cache_miss(self):
        path = self.out / "self_loop.aig"
        write_aig(path, dict(ni=0, nl=1, gates=[], outputs=[2], latches=[2]))
        a = p.Aiger(path)
        graph, base, step, reset = p.compile_graph(a)
        (free, _, _), mask = p.signatures(graph, [base, step, reset], p.Config(lanes=64))
        candidate = dict(root=1, recipe=[], out=0, witness_lane=(free[1] & -free[1]).bit_length()-1)
        context = dict(self.context, input_sha256=p.sha(path))
        qualified, report = prove_chunk(a, graph, dict(free=base, reset=reset, step=step), free, [candidate],
            self.out / "chunks/chunk_00000", self.solver, budget(), p.sha(path), self.solver_identity,
            inline_model_context=context)
        self.assertFalse(qualified)
        self.assertEqual(report["actual_queries"], 2)
        self.assertEqual(report["step_sat_model_cache_misses"], 1)
        self.assertEqual(candidate["proof"]["step"], "SAT")
        job = dict(self.job, case=dict(input=str(path), input_sha256=p.sha(path)))
        with patch.object(im.subprocess, "run", side_effect=AssertionError("duplicate solve")):
            samples, replay = im.collect_inline_models(a, graph, base, step, [candidate], self.out / "replay",
                                                       job, budget(), {})
        self.assertEqual(samples, [])
        self.assertEqual(replay["model_cache_misses"], 1)

    def test_missing_cached_model_collects_no_constraint_and_reports_miss(self):
        candidates, _, _ = self.prove()
        del candidates[0]["anytime_certificate"]["receipts"]["step"]["inline_image_model"]
        with patch.object(im.subprocess, "run", side_effect=AssertionError("duplicate solve")):
            samples, report = self.collect(candidates)
        self.assertEqual(samples, [])
        self.assertEqual(report["model_cache_misses"], 1)
        provenance = json.loads((self.out / "replay/provenance.json").read_text())
        self.assertEqual(provenance["model_unavailable"][0]["reason"], "MODEL_CACHE_MISS")
        self.assertEqual(candidates[0]["proof"]["step"], "SAT")

    def test_models_are_copied_before_subsequent_opposite_solve(self):
        broker = self.broker()
        answers, receipts = broker.solve([[2], [3]], "step")
        self.assertEqual(answers, [1, 1])
        bits = []
        for receipt in receipts:
            reference = receipt["inline_image_model"]
            batch = im.read_model_batch(broker.out, reference, broker.binding)
            bits.append(im.bound_model(receipt, reference, batch)["values"][0])
        self.assertEqual(bits, [1, 0])

    def test_nested_returned_receipt_mutation_cannot_poison_cache_or_peer(self):
        broker = self.broker()
        _, receipts = broker.solve([[2], [2]], "step")
        receipts[0]["inline_image_model"]["model_row"] = 999
        receipts[0]["assumptions"].append(4)
        self.assertEqual(receipts[1]["inline_image_model"]["model_row"], 0)
        self.assertEqual(receipts[1]["assumptions"], [2])
        _, again = broker.solve([[2]], "step")
        self.assertEqual(again[0]["inline_image_model"]["model_row"], 0)
        self.assertEqual(again[0]["assumptions"], [2])
        self.assertEqual(broker.metrics["actual_queries"], 1)

    def test_mutated_cached_model_rejected_without_a_subprocess(self):
        broker = self.broker()
        broker.solve([[2]], "step")
        next(broker.out.glob("*.models.jsonl")).write_text('{"query":0,"values":[0,0]}\n')
        with patch.object(im.subprocess, "run", side_effect=AssertionError("duplicate solve")):
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                broker.solve([[2]], "step")

    def test_changed_cnf_rejected_on_model_cache_hit(self):
        broker = self.broker()
        broker.solve([[2]], "step")
        broker.cnf.write_text("3 1\n1 0\n")
        with self.assertRaisesRegex(ValueError, "CNF changed"):
            broker.solve([[2]], "step")

    def test_assumption_order_remains_part_of_model_cache_key(self):
        broker = self.broker()
        broker.solve([[2, 4], [4, 2]], "step")
        self.assertEqual(broker.metrics["actual_queries"], 2)
        self.assertEqual(broker.metrics["inline_models_emitted"], 2)

    def test_bad_receipt_order_row_and_fingerprint_are_rejected(self):
        broker = self.broker()
        _, receipts = broker.solve([[2, 4], [3]], "step")
        source = receipts[0]
        reference = source["inline_image_model"]
        batch = im.read_model_batch(broker.out, reference, broker.binding)
        for alter in [lambda r: r.update(assumptions=[4, 2]), lambda r: r.update(row=1),
                      lambda r: r.update(cnf_sha256="0"*64), lambda r: r.update(result="UNKNOWN"),
                      lambda r: r["inline_image_model"].update(model_row=1),
                      lambda r: r.update(results_sha256="0"*64)]:
            row = copy.deepcopy(source); alter(row)
            with self.assertRaises(ValueError):
                im.bound_model(row, row["inline_image_model"], batch)

    def test_phase_source_solver_and_projection_binding_rejected(self):
        broker = self.broker()
        _, receipts = broker.solve([[2]], "step")
        ref = receipts[0]["inline_image_model"]
        for key, value in [("roles", dict(previous_inputs=[4], previous_state=[], current_inputs=[2])),
                           ("variables", [2, 1]), ("input_sha256", "0"*64),
                           ("source_hashes", {}), ("solver_sha256", "0"*64)]:
            expected = dict(broker.binding, **{key: value})
            with self.assertRaisesRegex(ValueError, "binding mismatch"):
                im.read_model_batch(broker.out, ref, expected)
        manifest = broker.out / ref["manifest_file"]
        value = json.loads(manifest.read_text()); value["phase"] = "reset"
        p.write_json(manifest, value)
        updated = dict(ref, manifest_sha256=p.sha(manifest))
        with self.assertRaisesRegex(ValueError, "phase/domain"):
            im.read_model_batch(broker.out, updated, broker.binding)

    def test_non_step_emission_never_requested(self):
        broker = self.broker()
        with patch.object(im.subprocess, "run", wraps=subprocess.run) as run:
            broker.solve([[2]], "reset")
            broker.solve([[4]], "free")
        self.assertTrue(all(len(call.args[0]) == 4 for call in run.call_args_list))
        self.assertFalse(list(broker.out.glob("*.models.jsonl")))

    def fake_model_result(self, status, models):
        broker = self.broker()
        def fake(command, **kwargs):
            Path(command[3]).write_text(f"query,result,conflicts,wall_s\n0,{status},0,0\n")
            Path(command[5]).write_text("".join(json.dumps(m)+"\n" for m in models))
            return subprocess.CompletedProcess(command, 0)
        with patch.object(im.subprocess, "run", side_effect=fake):
            return broker.solve([[2]], "step"), broker

    def test_missing_model_for_actual_sat_is_corruption(self):
        with self.assertRaisesRegex(ValueError, "missing/extra"):
            self.fake_model_result(1, [])

    def test_truncated_model_rejected(self):
        with self.assertRaisesRegex(ValueError, "incomplete/non-Boolean"):
            self.fake_model_result(1, [dict(query=0, values=[1])])

    def test_duplicate_model_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing/extra"):
            self.fake_model_result(1, [dict(query=0, values=[1, 0])]*2)

    def test_unknown_with_stale_model_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing/extra"):
            self.fake_model_result(0, [dict(query=0, values=[1, 0])])

    def test_unsat_with_stale_model_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing/extra"):
            self.fake_model_result(-1, [dict(query=0, values=[1, 0])])

    def test_unknown_has_no_model_and_is_not_cached(self):
        (answers, receipts), broker = self.fake_model_result(0, [])
        self.assertEqual(answers, [0])
        self.assertNotIn("inline_image_model", receipts[0])
        self.assertFalse(broker.cache)
        self.assertEqual(broker.metrics["unknown_not_cached"], 1)

    def test_original_recipe_replay_mandatory(self):
        candidates, _, _ = self.prove()
        with patch.object(im.p, "recipe_eval", return_value=0):
            # This fixture's failing root is 0 and its replacement is 1.
            with self.assertRaisesRegex(ValueError, "original-AIG recipe replay"):
                self.collect(candidates)

    def test_wrong_source_candidate_and_complement_rejected(self):
        candidates, _, _ = self.prove()
        for mutate in [lambda c: c.update(out=-3),
                       lambda c: c["anytime_certificate"]["miter_literals"].update(step=0),
                       lambda c: c["anytime_certificate"].update(candidate_index=99)]:
            rows = copy.deepcopy(candidates); mutate(rows[0])
            with self.assertRaises(ValueError):
                self.collect(rows, tag="bad_"+str(len(list(self.out.glob('bad_*')))))

    def test_cnf_hash_stream_exact(self):
        file = self.out / "graph.cnf"
        self.g.cnf(file)
        self.assertEqual(im.graph_cnf_sha256(self.g), p.sha(file))

    def test_zero_input_zero_latch_and_empty_role_vectors(self):
        for ni, nl in [(0, 1), (1, 0), (0, 0)]:
            directory = self.out / f"roles_{ni}_{nl}"; directory.mkdir()
            path = directory / "input.aig"
            write_aig(path, dict(ni=ni, nl=nl, gates=[], outputs=[0], latches=[0]*nl))
            a = p.Aiger(path); g, base, step, _ = p.compile_graph(a)
            roles, variables = im.d.projected_pis(g, base, step, a)
            for name in ("candidates.unproved.json", "query_literals.json"):
                p.write_json(directory/name, [])
            broker = im.InlineFrozenQueries(g, directory, self.solver, budget(), self.solver_identity,
                context=dict(self.context, roles=roles, variables=variables))
            answers, receipts = broker.solve([[1]], "step")
            self.assertEqual(answers, [1])
            batch = im.read_model_batch(directory, receipts[0]["inline_image_model"], broker.binding)
            self.assertEqual(len(batch[3][0]["values"]), 2*ni+nl)

    def test_real_unknown_budget_and_status_only_solver_differential(self):
        old = os.environ.get("STRAN2_SOLVER")
        if not old:
            self.skipTest("requires STRAN2_SOLVER for legacy differential")
        pigeons, holes = 9, 8
        nv = pigeons * holes + 2
        guard = 2 * (nv-1)
        var = lambda pigeon, hole: 2 * (1 + pigeon * holes + hole)
        clauses = [[1]]
        for pigeon in range(pigeons):
            clauses.append([guard ^ 1] + [var(pigeon, hole) for hole in range(holes)])
        for hole in range(holes):
            for pigeon in range(pigeons):
                for other in range(pigeon):
                    clauses.append([guard ^ 1, var(pigeon, hole) ^ 1, var(other, hole) ^ 1])
        cnf = self.out / "php.cnf"
        cnf.write_text(f"{nv} {len(clauses)}\n" + "".join(
            str(len(row)) + " " + " ".join(map(str, row)) + "\n" for row in clauses))
        queries = self.out / "php.queries"
        queries.write_text(f"3\n0 1 {guard}\n1 1 {guard^1}\n2 1 0\n")
        projection = self.out / "php.projection"
        projection.write_text(f"step {nv-1}\n" + " ".join(map(str, range(1, nv))) + "\n")
        models = self.out / "php.models.jsonl"
        results = []
        for name, solver, extra in [("old", old, []), ("new", self.solver, []),
                                   ("capture", self.solver, [str(projection), str(models)])]:
            output = self.out / (name + ".csv")
            process = subprocess.run([str(solver), str(cnf), str(queries), str(output), *extra],
                                     capture_output=True, text=True, timeout=10)
            self.assertEqual(process.returncode, 0, process.stderr)
            with output.open() as stream:
                results.append([{k: v for k, v in row.items() if k != "wall_s"} for row in csv.DictReader(stream)])
        self.assertEqual(results[0], results[1]); self.assertEqual(results[1], results[2])
        self.assertEqual([int(row["result"]) for row in results[0]], [0, 1, -1])
        self.assertEqual([json.loads(line)["query"] for line in models.read_text().splitlines()], [1])

    def test_solver_rejects_nonstep_projection_request(self):
        cnf, queries, projection = [self.out / name for name in ("bad.cnf", "bad.queries", "bad.projection")]
        cnf.write_text("2 1\n1 1\n"); queries.write_text("1\n0 1 2\n")
        projection.write_text("free 1\n1\n")
        process = subprocess.run([str(self.solver), str(cnf), str(queries), str(self.out / "bad.csv"),
                                  str(projection), str(self.out / "bad.models.jsonl")],
                                 capture_output=True, timeout=10)
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual((self.out / "bad.models.jsonl").read_text(), "")

    def test_complemented_or_overlapping_role_rejected(self):
        directory = self.out / "bad_roles"; directory.mkdir()
        for name in ("candidates.unproved.json", "query_literals.json"):
            p.write_json(directory/name, [])
        for current in ([3], [2]):
            with self.assertRaisesRegex(ValueError, "uncomplemented|independent"):
                im.InlineFrozenQueries(self.g, directory, self.solver, budget(), self.solver_identity,
                    context=dict(self.context, roles=dict(previous_inputs=[2], previous_state=[], current_inputs=current),
                                 variables=[1, current[0]//2]))


if __name__ == "__main__":
    unittest.main()
