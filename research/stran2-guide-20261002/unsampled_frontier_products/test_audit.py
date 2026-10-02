"""Small synthetic checks; never runs the mem audit or actual DSEC."""
import copy
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from types import SimpleNamespace
from unittest.mock import patch
from support import *
from proofs import fresh_proofs
from products import Products,check_selection,run_selection_family,dominance
from audit import calculate_changes
from test_frontier import fixture,write_aig,p
product=importlib.import_module('product')
global_module=module('test_global_original',PACKAGE/'global_expression_review/review.py')
hashdirect=module('test_hash_direct',PACKAGE/'nonlinear_divisors/hash_direct_audit.py')

def dl():return Deadline(time.monotonic()+60)
def full_witness(ia,c):
    values=ia.values([1,1],[1,1]);return dict(kind='candidate_local_free_SAT',inputs=[1,1],state=[1,1],
        root=values[c['root']],replacement=independent_recipe(c['recipe'],c['out'],values),global_lane=None,replay='PASS')

class AuditTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        self.path,self.a,self.ia,self.s,self.row,self.seq,self.free,self.cfg,self.c=fixture(self.root)
        self.c['free_witness']=full_witness(self.ia,self.c)
        self.abc=self.root/'abc-stub';self.abc.write_text('fixture, not executable')
    def tearDown(self):self.tmp.cleanup()
    def stub_product(self,mutate=False):
        def dsec(abc,original,path,out,seconds,tag):
            if mutate:Path(path).write_bytes(Path(path).read_bytes()+b'changed')
            log=Path(out)/(tag+'.log');log.write_text('fixture PASS\n')
            return dict(status='PASS',wall_s=0.0,log_sha256=sha(log))
        return SimpleNamespace(rebuild=product.rebuild,write_aig=product.write_aig,dsec=dsec)
    def emitter(self,mutate=False):
        out=self.root/'products';out.mkdir()
        return Products(p,self.stub_product(mutate),self.a,self.ia,global_module,self.path,self.abc,out,dl(),Bindings())
    def test_exact_old_subset_cumulative_changes(self):
        other=dict(self.c,root=8)
        changes=calculate_changes([self.c],[self.c,other])
        self.assertEqual(changes['removed'],[]);self.assertEqual(len(changes['retained']),1);self.assertEqual(len(changes['added']),1)
    def test_candidate_cost_and_full_witness_checks(self):
        self.assertTrue(verify_candidate(p,self.s,self.ia,self.c))
        c=copy.deepcopy(self.c);c['conservative_gain']+=1
        with self.assertRaises(ValueError):verify_candidate(p,self.s,self.ia,c)
        c=copy.deepcopy(self.c);c['free_witness']['state']=[0,0]
        with self.assertRaises(ValueError):verify_candidate(p,self.s,self.ia,c)
    def test_whole_original_later_alias_demoted(self):
        path=self.root/'later.aig'
        write_aig(path,2,2,[(6,8),(7,9),(11,13),(2,4),(14,16),(6,16)],[0,0],[18])
        a=p.Aiger(path);s=p.Structure(a);h=global_module.OriginalHash(global_module.Aig(path))
        row=classify(h,s,self.c)
        self.assertEqual(row['later_safe_original_aliases'],[20]);self.assertEqual(row['global_live_fresh_gates'],0)
        graph=product.rebuild(a,[self.c])
        self.assertEqual(genuine_ids([self.c],graph['realization'],{cid(self.c):row}),set())
    def test_genuine_requires_every_live_new_condition(self):
        cl={cid(self.c):dict(safe_original_aliases=[],global_live_fresh_gates=1)}
        good=dict(root=9,output_is_new=True,output_is_live=True,live_created_gates=1)
        self.assertEqual(genuine_ids([self.c],[good],cl),{cid(self.c)})
        for key,value in [('output_is_new',False),('output_is_live',False),('live_created_gates',0)]:
            row=dict(good,**{key:value});self.assertEqual(genuine_ids([self.c],[row],cl),set())
    def test_removal_never_reselects(self):
        emitter=self.emitter();cl={cid(self.c):dict(safe_original_aliases=[],global_live_fresh_gates=1)}
        with patch.object(product,'select',side_effect=AssertionError('reselection forbidden')):
            result=run_selection_family(p,self.s,product,emitter,'arm/raw',[self.c],cl,{cid(self.c)})
        self.assertEqual(result['same_selected_subsets']['without_new_identities'],[])
        self.assertEqual(result['all_genuine_build_same_set_marginal'],3)
        self.assertEqual(result['new_genuine_build_same_set_marginal'],3)
        self.assertEqual(emitter.cost_summary()['fresh_dsec_runs'],2)
    def test_alias_removed_by_new_identity_but_kept_in_no_genuine(self):
        row=dict(root=9,output_is_new=True,output_is_live=True,live_created_gates=1)
        cl={cid(self.c):dict(safe_original_aliases=[20],global_live_fresh_gates=0)}
        sets,g=removal_sets([self.c],[row],cl,{cid(self.c)})
        self.assertEqual(sets['without_new_identities'],[]);self.assertEqual(sets['without_all_genuine'],[self.c]);self.assertEqual(g,set())
    def test_shared_direct_scope_and_full_grammar_extras(self):
        second=dict(self.c,recipe=[8,16]);selections={'old':[self.c],'union':[second]}
        directs,scope=direct_scope(p,self.s,hashdirect,selections,{9:self.row['pool']},2)
        self.assertEqual(len(scope),1);self.assertEqual(scope[0]['used_divisors'],[3,4,8])
        expected={0,1}|{2*n+b for n in self.row['pool'] for b in (0,1)}|set(hashdirect.collect_hash_direct(self.s,9,self.row['pool'],2))
        self.assertEqual({c['out'] for c in directs},expected)
        self.assertTrue(set(scope[0]['hash_extras']) >= {10,11,12,13})
    def test_duplicate_roots_and_dependency_conflicts_rejected(self):
        ok,reason=check_selection(p,self.s,[self.c,self.c]);self.assertFalse(ok);self.assertEqual(reason,'same_root')
    def test_independent_dependency_cycle_rejected(self):
        graph=product.rebuild(self.a,[]);path=self.root/'base.aig';product.write_aig(path,graph)
        cyclic=dict(root=9,recipe=[],out=18)
        with self.assertRaisesRegex(ValueError,'cycle'):
            replay_independent(self.ia,[cyclic],path,global_module,self.path)
    def test_dsec_product_mutation_rejected(self):
        with self.assertRaisesRegex(ValueError,'changed'):
            self.emitter(mutate=True).emit('full',[self.c])
    def test_dsec_reuse_binds_every_product_and_selection(self):
        emitter=self.emitter();first,_=emitter.emit('one',[self.c]);second,_=emitter.emit('two',[self.c])
        self.assertFalse(first['dsec']['reused_exact_graph_dsec']);self.assertTrue(second['dsec']['reused_exact_graph_dsec'])
        self.assertEqual(second['dsec']['charged_new_wall_s'],0)
        path=emitter.out/'one/selection.json';path.write_bytes(path.read_bytes()+b'\n')
        with self.assertRaisesRegex(ValueError,'changed'):emitter.emit('three',[self.c])
    def test_later_dsec_cannot_mutate_prior_log(self):
        emitter=self.emitter();original=emitter.product.dsec;calls=[]
        def mutating(abc,source,path,out,seconds,tag):
            if calls:
                old=emitter.out/'one/dsec.log';old.write_bytes(old.read_bytes()+b'changed later')
            calls.append(str(path));return original(abc,source,path,out,seconds,tag)
        emitter.product.dsec=mutating
        emitter.emit('one',[self.c])
        with self.assertRaisesRegex(ValueError,'changed'):emitter.emit('two',[])
    def test_emitted_product_result_is_immutable(self):
        emitter=self.emitter();emitter.emit('one',[self.c])
        file=emitter.out/'one/result.json';file.write_bytes(file.read_bytes()+b'\n')
        with self.assertRaisesRegex(ValueError,'changed'):emitter.emitted.check()
    def test_dominance_holds_other_choices_and_dsec_best(self):
        emitter=self.emitter();full,_=emitter.emit('full',[self.c])
        directs=[dict(root=9,recipe=[],out=0,**self.s.cost(9,[],0)),dict(root=9,recipe=[],out=6,**self.s.cost(9,[],6))]
        rows=dominance(p,self.s,product,emitter,'dominance',[self.c],directs,full)
        self.assertEqual(rows[0]['alternatives'][0]['literal'],0)
        self.assertEqual(rows[0]['alternatives'][0]['and_count'],0)
        self.assertEqual(rows[0]['best_cheaper_direct_validated']['dsec']['status'],'PASS')
        self.assertEqual(rows[0]['alternatives'][1]['dsec'],'NOT_RUN')
    def test_fresh_build_and_direct_proofs_on_tiny_graph(self):
        solver=Path(os.environ['UNSAMPLED_SOLVER']);bound=Bindings();bound.add(solver);bound.add(self.path)
        valid,report=fresh_proofs(p,self.a,self.ia,[self.c],solver,self.root/'proof_build',dl(),bound,True)
        self.assertEqual(report['queries'],3);self.assertEqual(len(valid),1)
        self.assertEqual(valid[0]['proof']['free'],'SAT');self.assertTrue(valid[0]['proof']['free_witness_replayed'])
        d=dict(root=9,recipe=[],out=0,**self.s.cost(9,[],0))
        valid,report=fresh_proofs(p,self.a,self.ia,[d],solver,self.root/'proof_direct',dl(),bound,False)
        self.assertEqual(len(valid),1);self.assertEqual(report['queries'],3)
    def test_fresh_unknown_build_rejected_no_retry(self):
        fake=self.root/'unknown.py';fake.write_text('#!/usr/bin/env python3\nimport pathlib,sys\nn=int(pathlib.Path(sys.argv[2]).read_text().splitlines()[0])\npathlib.Path(sys.argv[3]).write_text("query,result,conflicts,wall_s\\n"+"".join(f"{i},0,1000,0.0\\n" for i in range(n)))\n');fake.chmod(0o755)
        bound=Bindings();bound.add(fake)
        with self.assertRaisesRegex(ValueError,'reproof'):fresh_proofs(p,self.a,self.ia,[self.c],fake,self.root/'unknown',dl(),bound,True)
        self.assertTrue((self.root/'unknown/obligations.results.csv').exists())
    def test_terminal_review_old_hash_rejects_current_rehash(self):
        source=self.root/'run';source.mkdir();file=source/'result.json';write_new(file,dict(original=True))
        ledger=self.root/'ledger.json';write_new(ledger,dict(status='PASS',source_manifest_sha256='fixture',
            original_run_files=1,run_bindings={str(file.resolve()):sha(file)}))
        final=dict(source_manifest_sha256='fixture',evidence={str(ledger):sha(ledger)})
        bind_reviewed_run(final,source,Bindings())
        file.write_text('{"changed":true}\n')
        current=Bindings();current.add(file)  # A current-byte snapshot alone would accept this.
        with self.assertRaisesRegex(ValueError,'identity mismatch'):bind_reviewed_run(final,source,current)
    def test_terminal_review_extra_file_rejected(self):
        source=self.root/'run';source.mkdir();file=source/'result.json';write_new(file,{})
        ledger=self.root/'ledger.json';write_new(ledger,dict(status='PASS',source_manifest_sha256='fixture',
            original_run_files=1,run_bindings={str(file.resolve()):sha(file)}))
        final=dict(source_manifest_sha256='fixture',evidence={str(ledger):sha(ledger)})
        (source/'extra').write_text('unreviewed')
        with self.assertRaisesRegex(ValueError,'file set'):bind_reviewed_run(final,source,Bindings())
    def test_gate_without_parent_go_does_not_execute(self):
        review=self.root/'review.json';write_new(review,{})
        out=self.root/'never'
        r=subprocess.run([sys.executable,'-B',str(HERE/'audit.py'),'--out',str(out),'--solver','/missing','--abc','/missing',
            '--diagnostic-review',str(review),'--review',str(review)],capture_output=True)
        self.assertNotEqual(r.returncode,0);self.assertFalse(out.exists());self.assertIn(b'GO required',r.stderr)

if __name__=='__main__':unittest.main()
