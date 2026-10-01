#!/usr/bin/env python3
"""Source binding and exact-receipt reuse regressions for online attribution."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest

import audit_online_products as audit
from diagnostic import load_runtime
p=load_runtime(Path(__file__).resolve().parent.parent)


class Tests(unittest.TestCase):
    def test_notice_preserves_earliest_best_and_deadline(self):
        first=dict(directory='checkpoint_00001',gain=4,supervisor_observed_elapsed_s=5)
        later=dict(directory='checkpoint_00002',gain=4,supervisor_observed_elapsed_s=7)
        r=dict(driver=dict(observed_checkpoints=[first,later],hard_transform_budget_s=6),
               selected_checkpoint=dict(directory='/evidence/checkpoint_00001',gain=4))
        self.assertIs(audit.selected_notice(r),first)
        r['driver']['hard_transform_budget_s']=4
        with self.assertRaisesRegex(ValueError,'deadline'):audit.selected_notice(r)
        r['driver']['hard_transform_budget_s']=10;r['selected_checkpoint']['directory']='/evidence/checkpoint_00002'
        with self.assertRaisesRegex(ValueError,'not best'):audit.selected_notice(r)

    def make_receipts(self,root,codes):
        cnf=root/'obligations.cnf';cnf.write_text('p cnf 1 0\n');fingerprint=audit.sha(cnf)
        qs=[[2],[0],[4]];q=root/'proof.queries';q.write_text('3\n0 1 2\n1 1 0\n2 1 4\n')
        r=root/'proof.results.csv';r.write_text('query,result,conflicts,wall_s\n'+''.join(f'{i},{v},0,0\n'for i,v in enumerate(codes)))
        receipts=[dict(cnf_sha256=fingerprint,assumptions=qs[i],queries_file=q.name,queries_sha256=audit.sha(q),
            results_file=r.name,results_sha256=audit.sha(r),row=i,result={-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[v])for i,v in enumerate(codes)]
        return fingerprint,qs,receipts

    def test_receipt_checks_exact_cnf_assumptions_status_and_paths(self):
        with tempfile.TemporaryDirectory()as tmp:
            root=Path(tmp);fingerprint,qs,receipts=self.make_receipts(root,[1,-1,-1]);receipt=receipts[0]
            self.assertEqual(audit.checked_receipt(receipt,fingerprint,qs[0],root)[0],1)
            for change,pattern in [(dict(cnf_sha256='bad'),'CNF'),(dict(assumptions=[3]),'CNF'),
                                   (dict(result='UNSAT'),'status'),(dict(row=1),'row'),
                                   (dict(queries_file='../proof.queries'),'unsafe')]:
                with self.assertRaisesRegex(ValueError,pattern):audit.checked_receipt(dict(receipt,**change),fingerprint,qs[0],root)

    def test_parsed_cache_still_checks_each_receipt_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);fingerprint,qs,receipts=self.make_receipts(root,[1,-1,-1]);cache={}
            self.assertEqual(audit.checked_receipt(receipts[0],fingerprint,qs[0],root,cache)[0],1)
            self.assertEqual(audit.checked_receipt(receipts[1],fingerprint,qs[1],root,cache)[0],-1)
            bad=dict(receipts[1],results_sha256='wrong')
            with self.assertRaisesRegex(ValueError,'changed'):audit.checked_receipt(bad,fingerprint,qs[1],root,cache)

    def run_reuse(self,codes):
        with tempfile.TemporaryDirectory()as tmp:
            root=Path(tmp);reuse=root/'old';reuse.mkdir();out=root/'new';out.mkdir()
            fingerprint,qs,receipts=self.make_receipts(reuse,codes)
            candidate=dict(root=4,recipe=[],out=2,conservative_gain=1)
            saved=dict(candidate,proof=dict(zip(('free','reset','step'),[r['result']for r in receipts])),
                       proof_receipts=dict(zip(('free','reset','step'),receipts)),sequentially_proved=codes[1:]==[-1,-1])
            order=[dict(query=i)for i in range(3)]
            audit.write_json(reuse/'candidates.json',[saved]);audit.write_json(reuse/'query_order.json',order)
            audit.write_json(reuse/'report.json',dict(cnf_sha256=fingerprint))
            calls=[]
            def solve(queries,phase):calls.append((queries,phase));return [-1]*len(queries),[dict(result='UNSAT')]*len(queries)
            broker=SimpleNamespace(fingerprint=fingerprint,solve=solve)
            answers,newreceipts,count=audit.reused_direct_answers(broker,[candidate],qs,order,reuse,out)
            return answers,count,calls

    def test_unknown_receipts_are_requeried(self):
        answers,count,calls=self.run_reuse([1,-1,0])
        self.assertEqual(answers,[1,-1,-1]);self.assertEqual(count,2)
        self.assertEqual(calls,[([[4]],'unknown_recheck')])

    def test_only_exact_conclusive_receipts_skip_solver(self):
        answers,count,calls=self.run_reuse([1,-1,-1])
        self.assertEqual(answers,[1,-1,-1]);self.assertEqual(count,3);self.assertEqual(calls,[])

    def test_copied_input_or_bound_evidence_drift_is_rejected(self):
        with tempfile.TemporaryDirectory()as tmp:
            path=Path(tmp)/'input.aig';path.write_bytes(b'original');bound={};audit.bind_files(bound,[path]);audit.verify_bound(bound)
            path.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError,'changed'):audit.verify_bound(bound)
            with self.assertRaisesRegex(ValueError,'changed'):audit.bind_files(bound,[path])

    def test_missing_or_unvalidated_cases_are_not_zero(self):
        rows=[dict(case='a',loaded_and=100,validated_conditional_fresh_build_marginal=3,original_search_complete=True),
              dict(case='b',loaded_and=1000,validated_conditional_fresh_build_marginal=None),
              dict(case='c',loaded_and=200,validated_conditional_fresh_build_marginal=0,original_search_complete=False)]
        report=audit.aggregate(rows)
        self.assertEqual(report['validated']['cases'],2);self.assertEqual(report['validated']['gain'],3)
        self.assertAlmostEqual(report['validated']['equal_case_percent'],1.5)
        self.assertEqual(report['excluding_largest_contributor']['cases'],1)

    def test_matched_grammar_includes_outputs_outside_pool(self):
        helper=Path(__file__).resolve().parent.parent/'nonlinear_divisors/hash_direct_audit.py'
        spec=importlib.util.spec_from_file_location('test_hash_direct_helper',helper);h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
        a=SimpleNamespace(ni=3,nl=0,m=7,na=4,no=1,gates=[(2,4),(8,6),(10,2),(12,8)],outputs=[14],latches=[])
        s=p.Structure(a);raw=h.collect_hash_direct(s,7,[1,2,3,4,5])
        self.assertIn(12,raw)
        self.assertEqual(p.normalize(s,7,raw[12]['recipe'],raw[12]['out']),([],12))
        self.assertNotIn(6,[1,2,3,4,5])


if __name__=='__main__':unittest.main()
