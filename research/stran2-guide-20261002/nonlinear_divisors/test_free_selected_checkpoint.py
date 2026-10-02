"""Positive seeded-lane bridge→proof→product→checkpoint→auditor fixture."""
import copy
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import prototype as p
import anytime as at
import image_guided as ig
import inline_models as im
import free_guided as fg
from product import write_aig,dsec
from test_anytime import budget

@unittest.skipUnless(os.environ.get('STRAN2_INLINE_SOLVER'),'requires STRAN2_INLINE_SOLVER')
class SelectedAppendedWitnessTests(unittest.TestCase):
    def test_positive_appended_selected_checkpoint_and_full_auditor(self):
        preserve=os.environ.get('STRAN2_FREE_POSITIVE_FIXTURE_OUT')
        if preserve:
            out=Path(preserve);out.mkdir(parents=True,exist_ok=False)
        else:
            tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);out=Path(tmp.name)
        # G is a conjunction of20 independent PIs. Seeded256 free lanes miss
        # G & (q0 XOR q1), while q0'=q1'=x0 proves the target relation.
        ni,nl=20,4;nci=ni+nl;gates=[]
        def land(x,y):
            gates.append((x,y));return 2*(nci+len(gates))
        h=4
        for node in range(3,ni+1):h=land(h,2*node)
        g=land(2,h);q0,q1,v,flag=[2*(ni+i) for i in range(1,5)]
        target=land(land(2,q0),h)
        next_v=land(q0,q1^1)
        source_root=land(v,flag)
        path=out/'input.aig';write_aig(path,dict(ni=ni,nl=nl,gates=gates,
            outputs=[g,target,source_root],latches=[2,2,next_v,g]))
        a=p.Aiger(path);graph,base,step,reset=p.compile_graph(a);maps=dict(free=base,reset=reset,step=step)
        cfg=p.Config();(free,_,_),mask=p.signatures(graph,[base,step,reset],cfg);structure=p.Structure(a)
        recipe,expr=p.normalize(structure,target//2,[g,q1],-2)
        self.assertEqual(p.recipe_eval(recipe,expr,free,mask)^free[target//2],0)
        source=dict(root=source_root//2,recipe=[],out=0,**structure.cost(source_root//2,[],0))
        difference=free[source['root']];self.assertTrue(difference)
        source['witness_lane']=(difference&-difference).bit_length()-1
        solver=Path(os.environ['STRAN2_INLINE_SOLVER']);identity,solver_hash=at.bind_executable(solver)
        runtime=list(dict.fromkeys(at.RUNTIME+ig.RUNTIME+im.RUNTIME+fg.RUNTIME))
        source_hashes={name:p.sha(p.PACKAGE/name) for name in runtime}
        job=dict(case=dict(input=str(path),input_sha256=p.sha(path)),out=str(out),config=vars(cfg),
                 source_hashes=source_hashes,solver_sha256=solver_hash,inline_image_models=True,predecessor_free=True,chunk_roots=32)
        p.write_json(out/'job.json',job)
        context=dict(input_sha256=p.sha(path),source_hashes=source_hashes,solver_sha256=solver_hash)
        at.prove_chunk(a,graph,maps,free,[source],out/'chunks/chunk_00000',solver,budget(),p.sha(path),identity,
                       inline_model_context=context)
        self.assertEqual({k:source['proof'][k] for k in ['free','reset','step']},dict(free='SAT',reset='UNSAT',step='SAT'))
        helper=fg.PredecessorFreeDomain(a,graph,base,step,free,mask,job,cfg,budget())
        targetdir=out/'model_replay';_,report=im.collect_inline_models(a,graph,base,step,[source],targetdir,job,budget(),{})
        rows=json.loads((targetdir/'replayed_models.json').read_text());admission=helper.admit([source],targetdir,report,rows)
        self.assertEqual(admission['added'],1)
        snap=helper.state.snapshot()
        c=dict(root=target//2,recipe=recipe,out=expr,witness_lane=256,**structure.cost(target//2,recipe,expr))
        self.assertGreater(c['conservative_gain'],0);helper.annotate([c])
        qualified,_=at.prove_chunk(a,graph,maps,snap.signatures,[c],out/'chunks/chunk_00001',solver,budget(),p.sha(path),identity,
                                  inline_model_context=context,free_domain_required=True)
        self.assertEqual(qualified,[c]);self.assertEqual(c['free_witness']['lane'],256)
        clock=budget();events=[]
        def event(row):events.append(dict(row,supervisor_observed_elapsed_s=time.monotonic()-clock.start))
        with patch.object(at,'emit',side_effect=event):
            product=at.publish_checkpoint(path,qualified,out,0,clock,p.sha(path),{})
        self.assertEqual(product['exact_same_selected_set_build_gain'],1)
        notice=events[0];checkpoint,_=at.verify_checkpoint(out,notice,p.sha(path),free_domain_required=True)
        result=dict(driver=dict(observed_checkpoints=[notice],hard_transform_budget_s=clock.end-clock.start),
                    selected_checkpoint=dict(directory=str(checkpoint),gain=notice['gain']))
        sys.path.insert(0,str(p.PACKAGE/'image_cegar_diagnostic'))
        import audit_online_products as audit
        destination=out/'selected_audit';destination.mkdir();bound={}
        with patch.object(im.subprocess,'run',side_effect=AssertionError('auditor re-solved original model')):
            audit.validate_selected(p,__import__('product'),at,out,result,job,path,destination,bound)
        audit.verify_bound(bound)
        audit_result=json.loads((destination/'source_proof_validation.json').read_text())
        self.assertEqual(audit_result['free_domain_validation']['selected_appended_witnesses'],1)
        self.assertEqual(audit_result['free_domain_validation']['authenticated_distinct_source_models'],1)
        if os.environ.get('STRAN2_ABC'):
            dsec_result=dsec(Path(os.environ['STRAN2_ABC']),path,checkpoint/'product.aig',out,30,'appended_product_dsec')
            self.assertEqual(dsec_result['status'],'PASS')
        else:dsec_result=dict(status='NOT_RUN',reason='set STRAN2_ABC')
        # Preserve original successful evidence. Only a separate copied source
        # is corrupted for the stale raw-model rejection.
        copied=out/'fault_copy';copied.mkdir()
        for name in ('chunks','free_domains','checkpoints'):shutil.copytree(out/name,copied/name)
        fault_job=dict(job,out=str(copied));p.write_json(copied/'job.json',fault_job)
        model_file=next((copied/'chunks/chunk_00000').glob('*.models.jsonl'));model_file.write_text(model_file.read_text()+'\n')
        fault_result=copy.deepcopy(result);fault_result['selected_checkpoint']['directory']=str(copied/'checkpoints'/checkpoint.name)
        fault_audit=out/'fault_audit';fault_audit.mkdir()
        with patch.object(im.subprocess,'run',side_effect=AssertionError('audit unexpectedly solved')):
            with self.assertRaisesRegex(ValueError,'hash mismatch'):
                audit.validate_selected(p,__import__('product'),at,copied,fault_result,fault_job,path,fault_audit,{})
        p.write_json(out/'fixture_result.json',dict(status='PASS',initial_lanes=256,selected_witness_lane=256,
            exact_build_gain=1,qualified=1,auditor_complete_free_domain=True,authenticated_source_model=True,
            stale_raw_model_rejected=True,dsec=dsec_result,formal_pilot=False,input_sha256=p.sha(path),solver_sha256=solver_hash,
            source_hashes=source_hashes,note='synthetic functionality fixture; no area-generalization or main-budget performance claim'))

if __name__=='__main__':unittest.main()
