"""Tiny synthetic fixtures only. No fixed-cohort search or timing experiment."""
from __future__ import annotations
import copy
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from common import *
from independent_aig import Aig
from search import search_unsampled
from proof import prove, validate_model, revalidate_receipts
from run import supervise, accept_completed

FROZEN = read(PACKAGE/'free_domain_diagnostic/runs/diagnostic-v1/045_mem_ctrl/frozen_inputs.json')
p = load_runtime(FROZEN)

def write_aig(path, ni, nl, gates, latches, outputs):
    def varint(x):
        out = bytearray()
        while x >= 128:
            out.append((x&127)|128)
            x >>= 7
        out.append(x)
        return out
    with path.open('xb') as f:
        f.write(f'aig {ni+nl+len(gates)} {ni} {nl} {len(outputs)} {len(gates)}\n'.encode())
        for x in latches+outputs:
            f.write(f'{x}\n'.encode())
        for node, (x, y) in enumerate(gates, ni+nl+1):
            x, y = max(x, y), min(x, y)
            f.write(varint(2*node-x)+varint(x-y))

def fixture(root, next_values=(0, 0)):
    path = root/'toy.aig'
    # root = (q XOR r) AND (a AND b); q'=r'=0 in the good fixture.
    write_aig(path, 2, 2, [(6, 8), (7, 9), (11, 13), (2, 4), (14, 16)], list(next_values), [18])
    a, ia = p.Aiger(path), Aig(path)
    s = p.Structure(a)
    cfg = p.Config()
    pool = [1, 2, 3, 4, 8]
    row = dict(root=9, pool=pool, pool_info={str(i): dict(roles=['fixture'], nonlinear=i>4) for i in pool})
    seq = [0]*(a.m+1)
    free = [0]*(a.m+1)
    # All four q=r=0 worlds: h=q&d and original root both zero.
    for lane in range(256):
        vals = ia.values([lane&1, (lane>>1)&1], [0, 0])
        for i, v in enumerate(vals):
            seq[i] |= v << lane
            free[i] |= v << lane
    candidate = dict(root=9, recipe=[6, 16], out=-2, discovery_domain='initial256_unsampled_difference')
    candidate.update(s.cost(9, candidate['recipe'], candidate['out']))
    return path, a, ia, s, row, seq, free, cfg, candidate

def deadline():
    return Deadline(time.monotonic()+30)

class SearchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.fixture = fixture(self.root)
    def tearDown(self):
        self.tmp.cleanup()
    def run_frontier(self, sentinels=()):
        _, a, ia, s, row, seq, free, cfg, c = self.fixture
        return search_unsampled(p, s, row, seq, (1<<256)-1, free, (1<<256)-1, cfg, deadline(), sentinels)
    def test_top8_separate_positive_normalized(self):
        found, stats, ranks = self.run_frontier()
        self.assertLessEqual(len(found), 8)
        self.assertGreater(stats['positive_unsampled_candidates'], 8)
        self.assertEqual(found, sorted(found, key=p.candidate_key))
        self.assertEqual(len(found), len({cid(c) for c in found}))
        for c in found:
            self.assertNotIn('witness_lane', c)
            self.assertGreater(c['conservative_gain'], 0)
            self.assertEqual(p.normalize(self.fixture[3], c['root'], c['recipe'], c['out']), (c['recipe'], c['out']))
    def test_no_baseline_mutation_and_disjoint(self):
        _, _, _, s, row, seq, free, cfg, _ = self.fixture
        before = copy.deepcopy((seq, free, row))
        normal, stats = p.search_root(s, row['root'], row['pool'], {int(k):v for k,v in row['pool_info'].items()},
                                      seq, (1<<256)-1, free, (1<<256)-1, cfg, deadline())
        added, _, _ = self.run_frontier()
        self.assertFalse({cid(c) for c in normal}&{cid(c) for c in added})
        self.assertEqual(before, (seq, free, row))
        self.assertEqual(normal, [])
    def test_passive_rank_does_not_inject(self):
        first, stats, _ = self.run_frontier()
        sentinel = cid(self.fixture[-1])
        observed, same_stats, ranks = self.run_frontier([sentinel])
        self.assertEqual(first, observed)
        self.assertEqual(stats, same_stats)
        self.assertTrue(ranks[0]['eligible'])
        self.assertEqual(ranks[0]['retained'], sentinel in {cid(c) for c in first})
        self.assertFalse(ranks[0]['injected'])
    def test_deadline_prevents_search(self):
        _, _, _, s, row, seq, free, cfg, _ = self.fixture
        with self.assertRaises(TimeoutError):
            search_unsampled(p,s,row,seq,(1<<256)-1,free,(1<<256)-1,cfg,Deadline(time.monotonic()-1))
    def test_cap_cannot_be_tuned(self):
        _, _, _, s, row, seq, free, _, _ = self.fixture
        with self.assertRaisesRegex(ValueError, 'cap'):
            search_unsampled(p,s,row,seq,(1<<256)-1,free,(1<<256)-1,p.Config(candidates_per_root=9),deadline())
    def test_full_truth_bruteforce_eligibility_and_rank(self):
        _, _, _, s, row, seq, free, cfg, c = self.fixture
        # Independent full enumeration of raw syntax and reference-count costs.
        literals=[2*n+b for n in row['pool'] for b in (0,1)]
        allfound={}
        for j,x in enumerate(literals):
            for y in literals[j+1:]:
                if x == y^1: continue
                raw=[([x,y],o) for o in (-2,-3)]
                raw += [([x,y,z,w],o) for w in literals for z in (-2,-3) for o in (-4,-5)]
                for recipe,out in raw:
                    recipe,out=p.normalize(s,9,recipe,out)
                    if not recipe: continue
                    if p.recipe_eval(recipe,out,seq,(1<<256)-1)!=seq[9]:continue
                    if p.recipe_eval(recipe,out,free,(1<<256)-1)!=free[9]:continue
                    cost=s.cost(9,recipe,out)
                    if cost['conservative_gain']<=0 or not any(n>s.nci for n in p.external_nodes(recipe,out)):continue
                    q=dict(root=9,recipe=recipe,out=out,**cost)
                    allfound[cid(q)]=q
        expected=sorted(allfound.values(),key=p.candidate_key)
        actual,stats,ranks=self.run_frontier([cid(c)])
        self.assertEqual([cid(c) for c in actual],[cid(c) for c in expected[:8]])
        self.assertEqual(stats['positive_unsampled_candidates'],len(expected))
        self.assertEqual(ranks[0]['rank'],[cid(c) for c in expected].index(cid(c))+1)

class ModelTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        self.path,self.a,self.ia,_,_,_,_,_,self.c=fixture(self.root)
        self.g,self.base,_,_=p.compile_graph(self.a)
        self.miter=self.g.xor(self.base[9],p.graph_recipe(self.g,self.base,self.c['recipe'],self.c['out']))
        self.variables=[i for i,g in enumerate(self.g.gates) if i and g is None]
        self.bits=[1,1,1,1,0,0]  # Original root=0; q&(a&b)=1.
    def tearDown(self):self.tmp.cleanup()
    def check(self,variables=None,bits=None,assumptions=None,candidate=None):
        return validate_model(self.g,self.variables if variables is None else variables,
            self.bits if bits is None else bits,[self.miter] if assumptions is None else assumptions,
            self.a,self.ia,self.base,self.c if candidate is None else candidate)
    def test_full_original_replay(self):
        w=self.check();self.assertEqual(w['state'],[1,1]);self.assertIsNone(w['global_lane'])
        self.assertFalse(w['reachable_teacher']);self.assertEqual((w['root'],w['replacement']),(0,1))
    def test_missing_model_bit(self):
        with self.assertRaises(ValueError):self.check(bits=self.bits[:-1])
    def test_nonboolean_and_bool_rejected(self):
        for v in (True,2,-1,'1'):
            bits=self.bits[:];bits[0]=v
            with self.assertRaises(ValueError):self.check(bits=bits)
    def test_wrong_projection_order(self):
        with self.assertRaises(ValueError):self.check(variables=self.variables[::-1])
    def test_unsatisfied_assumption(self):
        with self.assertRaises(ValueError):self.check(assumptions=[self.miter^1])
    def test_wrong_candidate(self):
        q=copy.deepcopy(self.c);q['recipe']=[14,16]
        with self.assertRaises(ValueError):self.check(candidate=q)

class SolverTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.solver=Path(os.environ.get('UNSAMPLED_SOLVER',''))
        if not cls.solver.is_file():
            raise RuntimeError('UNSAMPLED_SOLVER must name the isolated built solver; never skip proof tests')
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        self.path,self.a,self.ia,_,_,_,_,_,self.c=fixture(self.root)
    def tearDown(self):self.tmp.cleanup()
    def call(self,candidates=None):
        return prove(p,self.a,self.ia,[self.c] if candidates is None else candidates,self.solver,
                     self.root/'proof',deadline(),{str(self.path):sha(self.path)})
    def test_fresh_triple_and_persisted_replay(self):
        cs,r=self.call();self.assertEqual(cs[0]['proof'],dict(free='SAT',reset='UNSAT',image='UNSAT'))
        self.assertTrue(cs[0]['qualified_offline_opportunity']);self.assertEqual(r['total_queries'],3)
        review=revalidate_receipts(p,self.a,self.ia,cs,self.root/'proof',deadline())
        self.assertEqual(review['full_models'],1)
    def test_comb_unsat_no_later_queries(self):
        q=copy.deepcopy(self.c);q['recipe']=[14,16]
        cs,r=self.call([q]);self.assertEqual(cs[0]['proof'],dict(free='UNSAT',reset='NOT_RUN',image='NOT_RUN'))
        self.assertEqual(r['total_queries'],1);self.assertNotIn('free_witness',cs[0])
    def test_free_unknown_no_retry_or_backfill(self):
        fake=self.root/'unknown.py'
        fake.write_text('#!/usr/bin/env python3\nimport pathlib,sys\nn=int(pathlib.Path(sys.argv[2]).read_text().splitlines()[0])\npathlib.Path(sys.argv[3]).write_text("query,result,conflicts,wall_s\\n"+"".join(f"{i},0,1000,0.0\\n" for i in range(n)))\nif len(sys.argv)==6:pathlib.Path(sys.argv[5]).write_text("")\n')
        fake.chmod(0o755)
        cs,r=prove(p,self.a,self.ia,[self.c],fake,self.root/'proof',deadline(),{})
        self.assertEqual(cs[0]['proof'],dict(free='UNKNOWN',reset='NOT_RUN',image='NOT_RUN'))
        self.assertEqual(r['total_queries'],1);self.assertFalse(cs[0]['qualified_offline_opportunity'])
    def test_reset_sat_skips_image(self):
        q=copy.deepcopy(self.c);q['recipe']=[3,17]
        cs,r=self.call([q]);self.assertEqual(cs[0]['proof']['reset'],'SAT')
        self.assertEqual(cs[0]['proof']['image'],'NOT_RUN');self.assertEqual(r['total_queries'],2)
    def test_image_sat_reject(self):
        other=self.root/'other';other.mkdir();_,a,ia,_,_,_,_,_,c=fixture(other,next_values=(2,4))
        cs,r=prove(p,a,ia,[c],self.solver,self.root/'proof',deadline(),{})
        self.assertEqual(cs[0]['proof'],dict(free='SAT',reset='UNSAT',image='SAT'))
        self.assertFalse(cs[0]['qualified_offline_opportunity'])
    def test_tamper_model_rejected(self):
        cs,r=self.call();f=self.root/'proof/free.models.jsonl';f.write_text(f.read_text().replace('1','0',1))
        with self.assertRaises(ValueError):revalidate_receipts(p,self.a,self.ia,cs,self.root/'proof',deadline())
    def test_raw_query_cnf_result_projection_bindings(self):
        for name in ('free.queries', 'obligations.cnf', 'free.results.csv', 'free.projection', 'source_bindings.json'):
            with self.subTest(file=name), tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);path,a,ia,_,_,_,_,_,c=fixture(root)
                cs,r=prove(p,a,ia,[c],self.solver,root/'proof',deadline(),{str(path):sha(path)})
                f=root/'proof'/name;f.write_bytes(f.read_bytes()+b'\n')
                with self.assertRaises(ValueError):revalidate_receipts(p,a,ia,cs,root/'proof',deadline())
    def test_missing_reordered_and_non_boolean_model_records(self):
        mutations=[[],[dict(query=1,values=[1,1,1,1,0,0])],
                   [dict(query=0,values=[1,1])], [dict(query=0,values=[1,1,1,1,0,True])],
                   [dict(query=0,values=[1,1,1,1,0,0]),dict(query=0,values=[1,1,1,1,0,0])]]
        for k,models in enumerate(mutations):
            with self.subTest(mutation=k), tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);path,a,ia,_,_,_,_,_,c=fixture(root)
                fake=root/'bad.py'
                fake.write_text('#!/usr/bin/env python3\nimport pathlib,sys,json\npathlib.Path(sys.argv[3]).write_text("query,result,conflicts,wall_s\\n0,1,0,0.0\\n")\npathlib.Path(sys.argv[5]).write_text("".join(json.dumps(x)+"\\n" for x in '+repr(models)+'))\n')
                fake.chmod(0o755)
                with self.assertRaises(ValueError):prove(p,a,ia,[c],fake,root/'proof',deadline(),{})
    def test_reset_and_image_unknown_never_qualify(self):
        for target in ('reset','image'):
            with self.subTest(phase=target), tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);path,a,ia,_,_,_,_,_,c=fixture(root)
                fake=root/'phases.py'
                fake.write_text('#!/usr/bin/env python3\nimport pathlib,sys,json\nphase=pathlib.Path(sys.argv[2]).stem\nn=int(pathlib.Path(sys.argv[2]).read_text().splitlines()[0])\nanswer=1 if phase=="free" else (0 if phase=='+repr(target)+' else -1)\npathlib.Path(sys.argv[3]).write_text("query,result,conflicts,wall_s\\n"+"".join(f"{i},{answer},0,0.0\\n" for i in range(n)))\nif len(sys.argv)==6:pathlib.Path(sys.argv[5]).write_text("".join(json.dumps(dict(query=i,values=[1,1,1,1,0,0]))+"\\n" for i in range(n)))\n')
                fake.chmod(0o755)
                cs,r=prove(p,a,ia,[c],fake,root/'proof',deadline(),{})
                self.assertFalse(cs[0]['qualified_offline_opportunity'])
                self.assertEqual(cs[0]['proof'][target],'UNKNOWN')
                if target=='reset':self.assertEqual(cs[0]['proof']['image'],'NOT_RUN')
    def test_passed_candidate_cost_metadata_rejected(self):
        cs,r=self.call();cs[0]['conservative_gain']+=1
        with self.assertRaisesRegex(ValueError,'persisted'):revalidate_receipts(p,self.a,self.ia,cs,self.root/'proof',deadline())
    def test_tamper_status_rejected(self):
        cs,r=self.call();cs[0]['proof']['free']='UNSAT'
        with self.assertRaises(ValueError):revalidate_receipts(p,self.a,self.ia,cs,self.root/'proof',deadline())
    def test_tamper_source_rejected(self):
        cs,r=self.call();self.path.write_bytes(self.path.read_bytes()+b'x')
        with self.assertRaises(ValueError):revalidate_receipts(p,self.a,self.ia,cs,self.root/'proof',deadline())
    def test_fabricated_lane_rejected(self):
        self.c['witness_lane']=0
        with self.assertRaises(ValueError):self.call()
    def test_duplicate_candidates_rejected(self):
        with self.assertRaises(ValueError):self.call([self.c,self.c])
    def test_extra_candidate_cap(self):
        with self.assertRaises(ValueError):self.call([dict(self.c,root=100+i) for i in range(257)])

class GuardTests(unittest.TestCase):
    def test_changed_or_missing_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'file';path.write_text('abc');b=Bindings();b.add(path);path.write_text('abd')
            with self.assertRaises(ValueError):b.check()
            path.unlink()
            with self.assertRaises(ValueError):b.check()
    def test_symlink_binding_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp);(p/'target').write_text('x');(p/'link').symlink_to(p/'target')
            with self.assertRaises(ValueError):Bindings().add(p/'link')
    def test_exclusive_outputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'out';write_new(p,{'x':1})
            with self.assertRaises(FileExistsError):write_new(p,{'x':2})
            self.assertEqual(read(p),{'x':1})
    def test_supervisor_terminates_owned_descendant(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);pid=root/'child.pid';script=root/'sleep.py'
            script.write_text('import subprocess,time,pathlib\np=subprocess.Popen(["sleep","30"])\npathlib.Path('+repr(str(pid))+').write_text(str(p.pid))\ntime.sleep(30)\n')
            result=supervise(lambda end:[sys.executable,str(script)],root,0.15)
            self.assertTrue(result['timed_out'])
            child=int(pid.read_text());stat=Path(f'/proc/{child}/stat')
            self.assertTrue(not stat.exists() or stat.read_text().split()[2]=='Z')
    def test_supervisor_kills_child_and_grandchild(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);pid=root/'grandchild.pid';mid=root/'middle.py';top=root/'top.py'
            mid.write_text('import subprocess,time,pathlib\np=subprocess.Popen(["sleep","30"])\npathlib.Path('+repr(str(pid))+').write_text(str(p.pid))\ntime.sleep(30)\n')
            top.write_text('import subprocess,time\nsubprocess.Popen(['+repr(sys.executable)+','+repr(str(mid))+'])\ntime.sleep(30)\n')
            r=supervise(lambda end:[sys.executable,str(top)],root,0.25)
            self.assertTrue(r['timed_out']);child=int(pid.read_text());stat=Path(f'/proc/{child}/stat')
            self.assertTrue(not stat.exists() or stat.read_text().split()[2]=='Z')
    def test_no_post_deadline_acceptance_even_zero_exit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            r=supervise(lambda end:[sys.executable,'-c','import time; time.sleep(0.4)'],root,0.05)
            self.assertTrue(r['timed_out'])
    def test_zero_exit_observed_after_deadline_is_rejected(self):
        class Fake:
            pid=987654321;returncode=0
            def wait(self,timeout=None):return 0
        with tempfile.TemporaryDirectory() as tmp, patch('run.subprocess.Popen',return_value=Fake()), \
             patch('run.os.killpg'), patch('run.time.monotonic',side_effect=[0.0,0.0,0.2]):
            r=supervise(lambda end:['unused'],Path(tmp),0.1)
            self.assertEqual(r['returncode'],0);self.assertTrue(r['timed_out'])
    def completion_fixture(self,root):
        work=root/'work';work.mkdir();(work/'proof').mkdir()
        write_new(work/'proof/candidates.json',[])
        write_new(work/'proof/report.json',dict(bindings={},candidate_count=0,free_queries=0,total_queries=0,qualified=0))
        write_new(work/'receipt_audit.json',dict(status='PASS',candidates=0,queries=0))
        write_new(work/'baseline_qualified_references.json',[])
        write_new(work/'cumulative_qualified_union.json',dict(baseline=[],additional=[],baseline_retained=0))
        outputs={str(f.relative_to(work)):sha(f) for f in work.rglob('*') if f.is_file()}
        write_new(work/'result.json',dict(case='toy',status='COMPLETE',output_artifacts=outputs,source_bindings={},
            additional_candidates=0,free_queries=0,proof_queries=0,additional_qualified=0,baseline_qualified=0))
        (root/'worker.log').write_text(json.dumps(dict(case='toy',status='COMPLETE',result_sha256=sha(work/'result.json')))+'\n')
        return work
    def test_completion_hash_chain_rejects_report_result_union_tampering(self):
        for name in ('proof/report.json','result.json','cumulative_qualified_union.json','receipt_audit.json'):
            with self.subTest(file=name), tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);work=self.completion_fixture(root);manifest=source_manifest()
                self.assertEqual(accept_completed('toy',work,root,manifest)['status'],'COMPLETE')
                f=work/name;f.write_bytes(f.read_bytes()+b'\n')
                with self.assertRaises(ValueError):accept_completed('toy',work,root,manifest)
    def test_completion_missing_or_duplicate_notice_rejected(self):
        for text in ('', 'duplicate'):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);work=self.completion_fixture(root)
                log=root/'worker.log';old=log.read_text();log.write_text('' if not text else old+old)
                with self.assertRaises(ValueError):accept_completed('toy',work,root,source_manifest())
    def test_optimized_execution_rejected_before_any_cohort_work(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)/'run'
            r=subprocess.run([sys.executable,'-O','-B',str(HERE/'run.py'),'--worker-case',CASES[0],
                '--deadline',str(time.monotonic()+30),'--manifest','/missing','--solver','/missing','--out',str(out)],capture_output=True)
            self.assertNotEqual(r.returncode,0);self.assertFalse(out.exists())
            self.assertIn(b'assertions must remain enabled',r.stderr)
    def test_added_nested_result_json_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);work=self.completion_fixture(root);manifest=source_manifest()
            write_new(work/'proof/result.json',dict(unbound='extra'))
            with self.assertRaisesRegex(ValueError,'artifact tree'):accept_completed('toy',work,root,manifest)
    def test_execution_gate_rejects_no_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)/'run'
            r=subprocess.run([sys.executable,'-B',str(HERE/'run.py'),'--out',str(out),'--solver','/missing'],capture_output=True)
            self.assertNotEqual(r.returncode,0);self.assertFalse(out.exists())

if __name__ == '__main__':
    unittest.main()
