#!/usr/bin/env python3
"""Audit receipt, witness, and retention regressions; no broad-case reruns."""
import copy
import importlib
import json
from pathlib import Path
import tempfile
import unittest

import audit_products as audit
import diagnostic
p = diagnostic.load_runtime(Path(__file__).resolve().parent.parent)
product = importlib.import_module('product')


class Circuit:
    def __init__(self, ni, nl, gates, latches, outputs):
        self.ni,self.nl,self.gates,self.latches,self.outputs=ni,nl,gates,latches,outputs
        self.initial=[0]*nl;self.m=ni+nl+len(gates);self.na=len(gates);self.no=len(outputs)
    def step(self,x,s):
        v=[0]+list(x)+list(s)
        for a,b in self.gates:v.append((v[a//2]^(a&1))&(v[b//2]^(b&1)))
        lit=lambda x:v[x//2]^(x&1)
        return [lit(x) for x in self.outputs],[lit(x) for x in self.latches],v


class Tests(unittest.TestCase):
    def test_output_never_enters_source_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);diag=root/'diagnostic';run=root/'anytime';diag.mkdir();run.mkdir()
            for out in (diag,run,diag/'new',run/'new'):
                with self.assertRaises(ValueError):audit.validate_output(out,diag,run)
            audit.validate_output(root/'new',diag,run)
            self.assertFalse((root/'new').exists())

    def fixture(self):
        a=Circuit(2,2,[(2,4),(2,6),(12,4)],[2,2],[10,14])
        s=p.Structure(a);g,b,t,r=p.compile_graph(a)
        (free,_,_),mask=p.signatures(g,[b,t,r],p.Config(lanes=32))
        c=dict(root=7,recipe=[8,10],out=-2,**s.cost(7,[8,10],-2))
        mismatch=free[7]^p.recipe_eval(c['recipe'],c['out'],free,mask)
        c['witness_lane']=(mismatch&-mismatch).bit_length()-1
        return a,s,g,b,t,r,free,c

    def test_independent_free_witness_rejects_tampering(self):
        a,s,g,b,t,r,free,c=self.fixture()
        audit.check_candidate(p,a,s,c,free)
        self.assertEqual(c['free_witness']['replay'],'PASS')
        c['free_witness']['root']^=1
        with self.assertRaisesRegex(ValueError,'saved free witness mismatch'):
            audit.check_candidate(p,a,s,c,free)

    def test_cost_and_direct_disguised_as_build_rejected(self):
        a,s,g,b,t,r,free,c=self.fixture()
        stale=copy.deepcopy(c);stale['conservative_gain']+=1
        with self.assertRaisesRegex(ValueError,'candidate cost mismatch'):
            audit.check_candidate(p,a,s,stale,free)
        c.update(recipe=[],out=2)
        with self.assertRaisesRegex(ValueError,'Direct Build'):
            audit.check_candidate(p,a,s,c,free)

    def test_direct_zero_gates_can_cost_more_than_build(self):
        # Build retains no old internal cone; Direct to deep internal gate does.
        a=Circuit(4,0,[(2,4),(10,6),(12,8),(14,6)],[],[16])
        s=p.Structure(a)
        build=dict(root=8,recipe=[2,8],out=-2,**s.cost(8,[2,8],-2))
        direct=dict(root=8,recipe=[],out=14,**s.cost(8,[],14))
        self.assertEqual((build['conservative_gain'],direct['conservative_gain']),(3,1))
        chosen,_=product.select(s,[direct,build])
        self.assertEqual(chosen,[build])
        base=len(product.rebuild(a,[])['gates'])
        self.assertEqual(base-len(product.rebuild(a,[build])['gates']),3)
        self.assertEqual(base-len(product.rebuild(a,[direct])['gates']),1)

    def test_receipts_reconstruct_and_reject_status_and_row_changes(self):
        a,s,g,b,t,r,free,c=self.fixture()
        c.update(diagnostic_proof=dict(free='SAT',reset='UNSAT',image='UNSAT'),qualified_offline_opportunity=True)
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);diag=root/'diagnostic'; proof=diag/'new_proofs';proof.mkdir(parents=True)
            qs,_=audit.append_triples(p,g,[('free',b),('reset',r),('step',t)],[c])
            g.cnf(proof/'obligations.cnf');(proof/'obligations.queries').write_text(audit.query_text(qs))
            (proof/'obligations.results.csv').write_text('query,result,conflicts,wall_s\n0,1,0,0\n1,-1,0,0\n2,-1,0,0\n')
            report={kind+'_sha256':audit.sha(proof/name) for kind,name in [('cnf','obligations.cnf'),('queries','obligations.queries'),('results','obligations.results.csv')]}
            audit.write_json(proof/'report.json',report);audit.write_json(proof/'candidates.json',[c])
            def verify(label):
                out=root/label;out.mkdir();graph,base,step,reset=p.compile_graph(a)
                return audit.verify_diagnostic_receipts(p,graph,[('free',base),('reset',reset),('step',step)],[],diag,out)
            self.assertEqual(len(verify('valid')),1)
            c['diagnostic_proof']['image']='SAT';audit.write_json(proof/'candidates.json',[c])
            with self.assertRaisesRegex(ValueError,'saved diagnostic proof'):verify('status_bad')
            c['diagnostic_proof']['image']='UNSAT';audit.write_json(proof/'candidates.json',[c])
            (proof/'obligations.results.csv').write_text('query,result,conflicts,wall_s\n0,1,0,0\n0,-1,0,0\n2,-1,0,0\n')
            report['results_sha256']=audit.sha(proof/'obligations.results.csv');audit.write_json(proof/'report.json',report)
            with self.assertRaisesRegex(ValueError,'row identity'):verify('row_bad')

    def test_replay_exact_same_set_differs_from_reselection(self):
        a=Circuit(3,0,[(2,4),(8,6),(10,4)],[],[12]);s=p.Structure(a)
        old=dict(root=6,recipe=[],out=10,**s.cost(6,[],10))
        new=dict(root=6,recipe=[2,6],out=-2,**s.cost(6,[2,6],-2))
        chosen,_=product.select(s,[old,new]);self.assertEqual(chosen,[new])
        baseline=len(product.rebuild(a,[])['gates'])
        together=len(product.rebuild(a,chosen)['gates']);old_only=len(product.rebuild(a,[old])['gates'])
        self.assertEqual(baseline-together,2)
        self.assertEqual(old_only-together,1)


if __name__=='__main__':unittest.main()
