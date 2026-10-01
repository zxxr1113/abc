#!/usr/bin/env python3
"""Domain, invalidation, retry and immutable-source tests for opt-in feedback."""
import copy
import json
import itertools
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import image_guided as ig
from anytime import bind_executable
from prototype import Config, Structure, signatures
from test_anytime import budget, fixture


class ProjectionTests(unittest.TestCase):
    def test_exact_and_projection_duplicates_are_not_constraints(self):
        roots = [dict(root=3, pool=[1, 2])]
        seq, mask = [0, 0, 0, 0, 0], 1
        samples = [[0,0,0,0,1], [0,1,0,0,1], [0,1,0,0,0], [0,0,1,1,0]]
        selected, rows = ig.select_new_samples(roots, seq, mask, samples,
                                               [(0,0), (1,0), (1,0), (0,1)], set())
        self.assertEqual([r["decision"] for r in rows], ["PROJECTION_REDUNDANT", "APPEND_IMAGE_CONSTRAINT",
                                                         "EXACT_DUPLICATE", "APPEND_IMAGE_CONSTRAINT"])
        self.assertEqual(selected, [samples[1], samples[3]])

    def test_projection_contains_target_and_every_pool_node(self):
        roots = [dict(root=4, pool=[1,2,3])]
        for node in (1,2,3,4):
            sample = [0] * 5
            sample[node] = 1
            chosen, rows = ig.select_new_samples(roots, [0]*5, 1, [sample], [(node,)], set())
            self.assertEqual(chosen, [sample])
            self.assertEqual(rows[0]["relevant_roots"], [4])

    def test_repeated_projection_with_distinct_domain_key_not_new(self):
        sample = [0,1,0]
        chosen, rows = ig.select_new_samples([dict(root=2,pool=[1])], [0,0,0], 1,
                                             [sample,sample], [(1,0),(1,1)], set())
        self.assertEqual(len(chosen), 1)
        self.assertEqual(rows[1]["decision"], "PROJECTION_REDUNDANT")

    def test_incomplete_or_nonboolean_sample_rejected(self):
        for sample in ([0], [0,True], [0,2]):
            with self.assertRaises(ValueError):
                ig.select_new_samples([dict(root=1,pool=[])], [0,0], 1, [sample], [(0,)], set())


class GuidanceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.out = Path(self.tmp.name)
        self.path, self.a, self.g, self.maps, self.free, self.free_mask, self.c = fixture(self.out, same_next=False)
        self.helper = self.out / "unused-helper"
        self.helper.write_text("helper identity")
        identity, digest = bind_executable(self.helper)
        self.seq = [0] * (self.a.m + 1)
        self.job = dict(case={"input_sha256":ig.p.sha(self.path)}, source_hashes={},
                        image_model_solver=str(self.helper), image_model_solver_sha256=digest,
                        image_model_solver_identity=identity)
        self.guidance = ig.ImageGuidance(self.a,self.g,self.maps["free"],self.maps["step"],
            self.seq,1,self.free,self.free_mask,Structure(self.a),Config(),self.job,budget(),identity)
        self.roots = [dict(root=7,pool=[1,2,3,4,5,6],pool_info={})]
        self.guidance.remember_search(7,self.roots[0]["pool"],{},[],{})

    def tearDown(self):
        self.tmp.cleanup()

    def test_no_model_query_for_unknown_or_proved(self):
        for free, reset, step in [("SAT","UNSAT","UNKNOWN"),("SAT","UNKNOWN","SAT"),
                                  ("SAT","UNSAT","UNSAT"),("UNKNOWN","UNSAT","SAT")]:
            candidate = dict(self.c, proof=dict(free=free,reset=reset,step=step))
            with patch.object(ig.d,"collect_models") as call:
                self.assertEqual(self.guidance.refine(self.roots,[candidate],self.out), [])
                call.assert_not_called()

    def test_attempted_semantic_identity_cannot_retry_across_versions(self):
        candidate = copy.deepcopy(self.c)
        self.guidance.annotate([candidate])
        self.guidance.mark_attempted([candidate])
        old = copy.deepcopy(candidate)
        self.guidance.version += 1
        rediscovered = copy.deepcopy(self.c)
        self.guidance.annotate([rediscovered])
        with self.assertRaisesRegex(ValueError,"unchanged candidate"):
            self.guidance.mark_attempted([rediscovered])
        self.assertEqual(candidate, old)
        self.assertEqual(candidate["image_guidance"]["teacher_version"],0)
        self.assertEqual(rediscovered["image_guidance"]["teacher_version"],1)

    def test_expired_total_deadline_stops_before_model_or_search(self):
        self.guidance.deadline.end = 0
        self.c["proof"] = dict(free="SAT",reset="UNSAT",step="SAT")
        with patch.object(ig.d,"collect_models") as model:
            with self.assertRaises(TimeoutError):
                self.guidance.refine(self.roots,[self.c],self.out)
            model.assert_not_called()

    def test_skip_rejects_root_pool_or_info_mismatch(self):
        for row in [dict(self.roots[0],root=6), dict(self.roots[0],pool=[1,2]),
                    dict(self.roots[0],pool_info={1: {"roles": ["changed"]}})]:
            with self.assertRaisesRegex(ValueError,"root/pool"):
                self.guidance.cached_search(row)
        with self.assertRaisesRegex(ValueError,"candidate/root"):
            self.guidance.remember_search(6,[1,2],{},[self.c],{})

    def test_skip_preserves_earlier_candidates_and_rejects_untried(self):
        self.guidance.remember_search(7,self.roots[0]["pool"],{},[self.c],{"signature_hits":12})
        with self.assertRaisesRegex(ValueError,"untried cached"):
            self.guidance.cached_search(self.roots[0])
        self.guidance.mark_attempted([self.c])
        original = copy.deepcopy(self.c)
        self.c["proof"] = {"step":"UNSAT"}
        with patch.object(ig.p,"search_root") as search:
            cached, stats = self.guidance.search_again(self.roots[0],changed=False)
            search.assert_not_called()
        self.assertEqual(cached,[original])
        self.assertEqual(stats,{"signature_hits":12})
        cached[0]["recipe"].append(999)
        self.assertEqual(self.guidance.cached_search(self.roots[0])[0],[original])

    def test_new_projection_restarts_only_relevant_root(self):
        roots = [dict(root=5,pool=[1],pool_info={}),dict(root=7,pool=[2],pool_info={})]
        guide = self.guidance
        guide.search_cache.clear()
        for r in roots: guide.remember_search(r["root"],r["pool"],{},[],{})
        sample = [0,1,0,0,0,1,0,0]
        added, decisions = ig.select_new_samples(roots,[0]*8,1,[sample],[(1,0)],set())
        self.assertEqual(decisions[0]["relevant_roots"],[5])
        guide.seq,guide.mask=ig.d.append_samples([0]*8,1,added)
        with patch.object(ig.p,"search_root",return_value=([],{})) as search:
            for r in roots: guide.search_again(r,r["root"] in decisions[0]["relevant_roots"])
        self.assertEqual(search.call_count,1)
        self.assertEqual(search.call_args.args[1],5)

    def test_duplicate_projection_preserves_signed_pair_recipes_and_full_topk(self):
        directory=self.out/"signed_pairs"
        directory.mkdir()
        _,circuit,g,maps,_,_,_=fixture(directory,same_next=True)
        config=Config(lanes=64)
        (free,image,reset),fm=signatures(g,[maps["free"],maps["step"],maps["reset"]],config)
        seq=[a | (b << config.lanes) for a,b in zip(image,reset)];mask=(1 << (2*config.lanes))-1
        copies=[[int((value >> lane)&1) for value in seq] for lane in [0,1,7,63,64,127,0]]
        expanded,extended_mask=ig.d.append_samples(seq,mask,copies)
        pool=self.roots[0]["pool"];literals=[2*n+phase for n in pool for phase in (0,1)]
        for a,b in itertools.product(literals,repeat=2):
            for output_phase in (0,1):
                recipes=[([a,b],-2-output_phase)]
                for c in literals:
                    recipes += [([a,b,-2-inner,c],-4-output_phase) for inner in (0,1)]
                for recipe,out in recipes:
                    self.assertEqual(ig.p.recipe_eval(recipe,out,seq,mask)==seq[7],
                                     ig.p.recipe_eval(recipe,out,expanded,extended_mask)==expanded[7])
        args=(Structure(circuit),7,pool,{})
        old,old_stats=ig.p.search_root(*args,seq,mask,free,fm,config,budget())
        new,new_stats=ig.p.search_root(*args,expanded,extended_mask,free,fm,config,budget())
        self.assertTrue(old)
        self.assertEqual(old,new)
        self.assertEqual(old_stats,new_stats)

    def test_changed_model_helper_rejected_before_query(self):
        self.helper.write_text("different")
        self.c["proof"] = dict(free="SAT",reset="UNSAT",step="SAT")
        with self.assertRaisesRegex(ValueError,"model executable identity"):
            self.guidance.refine(self.roots,[self.c],self.out)

    @unittest.skipUnless(os.environ.get("STRAN2_MODEL_SOLVER"),"set STRAN2_MODEL_SOLVER for integration")
    def test_real_model_replay_clone_pool_freeze_and_unknown_retry_exclusion(self):
        helper = Path(os.environ["STRAN2_MODEL_SOLVER"])
        identity, digest = bind_executable(helper)
        self.guidance.helper,self.guidance.helper_identity,self.guidance.helper_hash = helper,identity,digest
        self.c["proof"] = dict(free="SAT",reset="UNSAT",step="SAT")
        self.guidance.mark_attempted([self.c])
        old_graph = (copy.deepcopy(self.g.gates),copy.deepcopy(self.g.hash))
        old_roots = copy.deepcopy(self.roots)
        old_seq = list(self.seq)
        fresh = dict(self.c, recipe=[4,8], out=-2)
        with patch.object(ig.p,"search_root",return_value=([self.c,fresh],{})) as search:
            found = self.guidance.refine(self.roots,[self.c],self.out)
        self.assertEqual(found,[fresh])
        self.assertEqual((self.g.gates,self.g.hash),old_graph)
        self.assertEqual(self.roots,old_roots)
        self.assertEqual(self.seq,old_seq)
        self.assertEqual(self.guidance.version,1)
        self.assertGreater(self.guidance.mask,1)
        self.assertEqual(search.call_args.args[2],self.roots[0]["pool"])
        self.assertFalse(found[0]["image_guidance"]["reachable_teacher"])
        replay = json.loads((self.out/"image_guidance/round_00000/replayed_models.json").read_text())
        self.assertTrue(all(r["replay"] == "PASS" and r["domain"] == ig.DOMAIN for r in replay))
        self.guidance.mark_attempted(found)
        with patch.object(ig.d,"collect_models") as models:
            self.assertEqual(self.guidance.refine(self.roots,[self.c],self.out),[])
            models.assert_not_called()
        # A distinct state learns valid new constraints but must stop if capped
        # re-enumeration produces only identities already attempted (even UNKNOWN).
        second = self.out / "only_seen"
        second.mkdir()
        another = ig.ImageGuidance(self.a,self.g,self.maps["free"],self.maps["step"],
            self.seq,1,self.free,self.free_mask,Structure(self.a),Config(),self.job,budget(),identity)
        another.helper,another.helper_hash = helper,digest
        another.remember_search(7,self.roots[0]["pool"],{},[self.c],{})
        another.mark_attempted([self.c])
        with patch.object(ig.p,"search_root",return_value=([self.c],{})):
            self.assertEqual(another.refine(self.roots,[self.c],second),[])
        report = json.loads((second/"image_guidance/round_00000/refinement.json").read_text())
        self.assertEqual(report["stopping_reason"],"NO_UNTRIED_RETURNED_TOPK_CANDIDATE")
        self.assertEqual(another.version,1)


if __name__ == "__main__":
    unittest.main()
