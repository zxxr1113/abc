#!/usr/bin/env python3
"""Exact cone/reference, immutable-plan and model-domain adversarial tests."""
import copy
import dataclasses
import itertools
import json
import os
from pathlib import Path
import random
import tempfile
import unittest
from unittest.mock import patch

import inline_models as im
import prototype as p
from anytime import bind_executable, prove_chunk
from test_anytime import budget, fixture


def validator(graph, variables=None, deadline=None):
    variables = variables if variables is not None else [i for i,g in enumerate(graph.gates) if i and g is None]
    return im.ConeValidator(graph, variables, im.graph_cnf_sha256(graph), deadline)


class ConeTests(unittest.TestCase):
    def test_exhaustive_all_ordered_literal_pairs_match_full_reference(self):
        graph = p.Graph()
        # Unused input 3, constants/complements, reconvergence, and late PI 7.
        graph.gates = [None, None, None, None, (2,5), (8,3), (8,11), None, (14,12)]
        variables = [1,2,3,7]
        check = validator(graph, variables)
        literals = list(range(2*len(graph.gates)))
        queries = [(q,) for q in literals] + list(itertools.product(literals, repeat=2))
        for bits in itertools.product((0,1), repeat=len(variables)):
            values = im.d.graph_values(graph, variables, bits)
            for assumptions in queries:
                expected = tuple(values[q//2] ^ (q&1) for q in assumptions)
                self.assertEqual(check.evaluate(variables, bits, assumptions), expected)
        self.assertNotEqual(check.plan([2,4]), check.plan([4,2]))

    def test_seeded_random_dags_multiple_assumptions_match_reference(self):
        rng = random.Random(2026100207)
        for _ in range(30):
            graph = p.Graph()
            graph.gates += [None] * rng.randrange(6)
            for gate in range(24):
                if gate % 7 == 0:
                    graph.gates.append(None)
                else:
                    graph.gates.append((rng.randrange(2*len(graph.gates)), rng.randrange(2*len(graph.gates))))
            variables = [i for i,g in enumerate(graph.gates) if i and g is None]
            check = validator(graph, variables)
            for _ in range(40):
                bits = [rng.randrange(2) for _ in variables]
                values = im.d.graph_values(graph, variables, bits)
                assumptions = [rng.randrange(2*len(graph.gates)) for _ in range(rng.randrange(1,17))]
                self.assertEqual(check.evaluate(variables,bits,assumptions),
                                 tuple(values[q//2]^(q&1) for q in assumptions))

    def test_constants_zero_inputs_and_multiple_dependencies(self):
        empty = p.Graph()
        check = validator(empty, [])
        self.assertEqual(check.evaluate([],[],[0,1,1,0]), (0,1,1,0))
        self.assertEqual(check.plan([1]).gate_order, ())
        graph = p.Graph();graph.gates = [None,None,None,(2,4),(3,5)]
        check = validator(graph,[1,2])
        self.assertEqual({x[0] for x in check.plan([6,8]).gate_order}, {3,4})
        self.assertEqual(check.evaluate([1,2],[1,0],[2,3,6,9]),(1,0,0,1))

    def test_source_graph_mutation_does_not_change_frozen_plan(self):
        graph = p.Graph();graph.gates = [None,None,None,[2,4]]
        check = validator(graph,[1,2]);plan=check.plan([6])
        expected=check.evaluate([1,2],[1,1],[6],plan)
        graph.gates[3][1]=5
        graph.gates.append((2,3))
        self.assertEqual(check.evaluate([1,2],[1,1],[6],plan), expected)
        self.assertEqual(check.graph.gates, (None,None,None,(2,4)))
        with self.assertRaisesRegex(ValueError,'pure-definitional CNF'):
            im.ConeValidator(graph,[1,2],check.graph.cnf_sha256)

    def test_graph_and_plan_metadata_are_deeply_immutable(self):
        graph=p.Graph();graph.gates=[None,None,None,(2,4)]
        check=validator(graph);plan=check.plan([6])
        with self.assertRaises(dataclasses.FrozenInstanceError):
            check.graph.gates=()
        with self.assertRaises(TypeError):
            check.graph.gates[3][0]=3
        with self.assertRaises(dataclasses.FrozenInstanceError):
            plan.assumptions=(7,)
        with self.assertRaises(TypeError):
            plan.gate_order[0][0]=1

    def test_foreign_graph_even_same_literals_and_foreign_plan_rejected(self):
        one=p.Graph();one.gates=[None,None,None,(2,4)]
        two=p.Graph();two.gates=[None,None,None,(2,5)]
        a,b=validator(one),validator(two)
        with self.assertRaisesRegex(ValueError,'plan graph/assumption'):
            b.evaluate([1,2],[1,0],[6],a.plan([6]))
        same=validator(one)
        with self.assertRaisesRegex(ValueError,'plan graph/assumption'):
            same.evaluate([1,2],[1,1],[6],a.plan([6]))
        with self.assertRaisesRegex(ValueError,'plan graph/assumption'):
            a.evaluate([1,2],[1,1],[7],a.plan([6]))

    def test_mutating_assumption_input_cannot_mutate_cached_plan(self):
        graph=p.Graph();graph.pi();graph.pi();check=validator(graph)
        query=[2,4];plan=check.plan(query);query.reverse()
        self.assertEqual(plan.assumptions,(2,4))
        self.assertEqual(check.plan([2,4]),plan)
        with self.assertRaisesRegex(ValueError,'plan graph/assumption'):
            check.evaluate([1,2],[1,0],query,plan)

    def test_invalid_assumptions_rejected(self):
        graph=p.Graph();graph.pi();check=validator(graph)
        for assumptions in ([],[-1],[4],[True],[2]*17):
            with self.subTest(assumptions=assumptions),self.assertRaises(ValueError):
                check.evaluate([1],[1],assumptions)

    def test_all_unused_projected_bits_still_required_and_boolean(self):
        graph=p.Graph();graph.pi();graph.pi();check=validator(graph)
        self.assertEqual(check.plan([2]).required_pis,(1,))
        for variables,bits in [([1],[1]),([1,2],[1]),([1,2],[1,True]),([1,2],[1,2]),([1,1],[1,0]),([True,2],[1,0]),([2,1],[1,0])]:
            with self.subTest(variables=variables,bits=bits),self.assertRaises(ValueError):
                check.evaluate(variables,bits,[2])

    def test_unchecked_or_incomplete_projection_rejected(self):
        graph=p.Graph();graph.pi();graph.pi()
        for variables in ([1],[1,1],[0,1,2],[1,True],[1,2,3]):
            with self.assertRaises(ValueError):validator(graph,variables)

    def test_cycles_forward_edges_bad_literals_and_bad_constant_rejected(self):
        invalid=[[(0,0)], [None,None,(2,4)], [None,None,(2,6)], [None,None,(-1,2)],
                 [None,None,(True,2)], [None,None,(2,)], [None,None,(2,2,2)]]
        for gates in invalid:
            graph=p.Graph();graph.gates=gates
            with self.subTest(gates=gates),self.assertRaises(ValueError):validator(graph)

    def test_extra_out_of_cone_constraints_and_altered_cnf_rejected(self):
        graph=p.Graph();graph.pi();graph.pi();graph.land(2,4)
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/'graph.cnf';graph.cnf(path);original=path.read_text()
            alternatives=[original+'1 2\n',original.replace('1 1\n','1 0\n',1),
                          original.replace('3 3 5 6','3 2 5 6'),original.replace('2 4 7\n','')]
            for text in alternatives:
                path.write_text(text)
                with self.assertRaisesRegex(ValueError,'pure-definitional CNF'):
                    im.ConeValidator(graph,[1,2],p.sha(path))

    def test_deadline_checked_before_and_after_plan_construction(self):
        graph=p.Graph();graph.pi();graph.pi();graph.land(2,4)
        limit=budget();check=validator(graph,deadline=limit)
        limit.end=0
        with self.assertRaises(TimeoutError):check.plan([6])
        self.assertEqual(check.metrics['plans_built'],0)
        limit=budget();check=validator(graph,deadline=limit)
        with patch.object(limit,'remaining',side_effect=[1,TimeoutError('expired while building plan')]):
            with self.assertRaisesRegex(TimeoutError,'while building'):
                check.plan([6])
        self.assertEqual(check.metrics['plans_built'],0)
        self.assertFalse(check._plans)


@unittest.skipUnless(os.environ.get('STRAN2_INLINE_SOLVER'),'requires STRAN2_INLINE_SOLVER')
class ConeReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.solver=Path(os.environ['STRAN2_INLINE_SOLVER']);cls.identity,cls.digest=bind_executable(cls.solver)

    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.out=Path(self.tmp.name)
        self.path,self.a,self.graph,self.maps,self.free,self.mask,self.c=fixture(self.out,same_next=False)
        self.context=dict(input_sha256=p.sha(self.path),source_hashes={'test':'f'*64},solver_sha256=self.digest)
        prove_chunk(self.a,self.graph,self.maps,self.free,[self.c],self.out/'chunks/chunk_00000',
                    self.solver,budget(),p.sha(self.path),self.identity,inline_model_context=self.context)
        self.job=dict(case=dict(input=str(self.path),input_sha256=p.sha(self.path)),out=str(self.out),
                      solver_sha256=self.digest,source_hashes=self.context['source_hashes'],inline_image_models=True)

    def tearDown(self):self.tmp.cleanup()

    def collect(self,cone,tag):
        return im.collect_inline_models(self.a,self.graph,self.maps['free'],self.maps['step'],[self.c],
              self.out/tag,dict(self.job,inline_cone_check=cone),budget(),{})

    def test_same_original_samples_and_witnesses_no_new_solver(self):
        with patch.object(im.subprocess,'run',side_effect=AssertionError('no duplicate solve')):
            full,fr=self.collect(False,'full')
            with patch.object(im.d,'graph_values',side_effect=AssertionError('full compiled scan')), \
                 patch.object(self.a,'step',wraps=self.a.step) as step, \
                 patch.object(im.p,'recipe_eval',wraps=im.p.recipe_eval) as recipe:
                cone,cr=self.collect(True,'cone')
        self.assertEqual(step.call_count,2)
        self.assertEqual(recipe.call_count,1)
        self.assertEqual(full,cone)
        self.assertEqual(cr['additional_solver_queries'],0)
        self.assertEqual(cr['cone_validation']['models_checked'],1)
        a,b=[json.loads((self.out/tag/'replayed_models.json').read_text()) for tag in ['full','cone']]
        for rows in (a,b):
            for row in rows:row.pop('source_provenance_sha256')
        self.assertEqual(a,b)
        self.assertNotIn('compiled_model_validator',fr)

    def test_original_recipe_replay_still_mandatory(self):
        with patch.object(im.p,'recipe_eval',return_value=0):
            with self.assertRaisesRegex(ValueError,'original-AIG recipe replay'):
                self.collect(True,'bad_recipe')

    def test_independent_successor_replay_still_mandatory(self):
        original = self.a.step
        calls = []
        def broken(inputs, state):
            result = original(inputs, state)
            calls.append((inputs, state))
            if len(calls) == 1:
                return result[0], [0]*self.a.nl, result[2]
            return result
        with patch.object(self.a,'step',side_effect=broken):
            with self.assertRaisesRegex(ValueError,'original-AIG recipe replay'):
                self.collect(True,'bad_transition')
        self.assertEqual(len(calls),2)

    def test_wrong_model_receipt_and_role_metadata_still_rejected(self):
        self.c['anytime_certificate']['receipts']['step']['assumptions'][0]^=1
        with self.assertRaisesRegex(ValueError,'step receipt mismatch'):
            self.collect(True,'bad_receipt')

    def test_mutated_cached_model_artifact_still_rejected(self):
        chunk=self.out/'chunks/chunk_00000';model=next(chunk.glob('*.models.jsonl'))
        model.write_text(model.read_text().replace('1','0',1))
        with self.assertRaisesRegex(ValueError,'artifact hash mismatch'):
            self.collect(True,'bad_model')

    def test_model_cache_miss_keeps_sat_without_cone_plan(self):
        del self.c['anytime_certificate']['receipts']['step']['inline_image_model']
        with patch.object(im.ConeValidator,'__init__',side_effect=AssertionError('no model, no plan')):
            samples,report=self.collect(True,'missing')
        self.assertEqual(samples,[])
        self.assertEqual(report['model_cache_misses'],1)
        self.assertEqual(report['cone_validation'],{})
        self.assertEqual(self.c['proof']['step'],'SAT')


if __name__=='__main__':unittest.main()
