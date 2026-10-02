"""Opt-in predecessor-free bridge/controller regressions; no benchmark matrix."""
import copy
import json
import os
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch
import prototype as p
import anytime as at
import image_guided as ig
import inline_models as im
import free_guided as fg
from product import write_aig
from test_anytime import budget,fixture

SOLVER=os.environ.get('STRAN2_INLINE_SOLVER')

class ModeTests(unittest.TestCase):
    def test_mode_prerequisites_and_default_off(self):
        fg.validate_mode({},p.Config(lanes=64),1000)
        for job,cfg,chunk in [(dict(predecessor_free=True),p.Config(),32),
             (dict(predecessor_free=True,inline_image_models=True,image_model_solver='helper'),p.Config(),32),
             (dict(predecessor_free=True,inline_image_models=True),p.Config(lanes=64),32),
             (dict(predecessor_free=True,inline_image_models=True),p.Config(),33)]:
            with self.assertRaises(ValueError):fg.validate_mode(job,cfg,chunk)
        fg.validate_mode(dict(predecessor_free=True,inline_image_models=True),p.Config(),32)

    def test_worker_rejects_unsupported_mode_before_launch_or_checkpoint(self):
        job=dict(case={},config=vars(p.Config()),chunk_roots=32,predecessor_free=True)
        with patch.object(at,'publish_checkpoint') as publish,patch.object(at,'bind_executable') as bind:
            with self.assertRaisesRegex(ValueError,'requires original inline'):at.transform(job)
            publish.assert_not_called();bind.assert_not_called()

    def test_enabled_candidate_missing_provenance_fails_before_solver(self):
        with tempfile.TemporaryDirectory() as tmp:
            path,a,g,maps,free,mask,c=fixture(Path(tmp))
            with patch.object(at,'FrozenQueries') as solver:
                with self.assertRaisesRegex(ValueError,'lost provenance'):
                    at.prove_chunk(a,g,maps,free,[c],Path(tmp)/'chunks/chunk_00000',Path(tmp)/'unused',budget(),p.sha(path),free_domain_required=True)
                solver.assert_not_called()

    def test_free_off_guidance_has_no_extra_artifact_or_annotation(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp);path,a,g,maps,free,mask,c=fixture(out)
            guidance=ig.ImageGuidance(a,g,maps['free'],maps['step'],[0]*(a.m+1),1,free,mask,
                p.Structure(a),p.Config(),dict(case=dict(input_sha256=p.sha(path))),budget(),None)
            guidance.annotate([c]);self.assertNotIn('free_domain',c)
            self.assertIsNone(guidance.free_guidance);self.assertFalse((out/'free_domains').exists())
            self.assertNotIn('free_domain',guidance.report())

class ControllerFlowTests(unittest.TestCase):
    def run_mocked(self,union=False):
        temp=tempfile.TemporaryDirectory();self.addCleanup(temp.cleanup);out=Path(temp.name)
        path=out/'input.aig';write_aig(path,dict(ni=2,nl=1,gates=[(2,6),(8,4),(3,6),(12,4)],latches=[2],outputs=[10,14]))
        solver=out/'unused-solver';solver.write_text('identity only');identity,sh=at.bind_executable(solver)
        job=dict(case=dict(input=str(path),input_sha256=p.sha(path)),config=vars(p.Config()),chunk_roots=1,
                 predecessor_free=True,inline_image_models=True,start=time.monotonic(),end=time.monotonic()+30,
                 solver=str(solver),solver_sha256=sh,solver_identity=identity,source_hashes={},out=str(out))
        searches=[];proof_widths=[];published=[];old=[dict(identity=('old',i)) for i in range(49)];new=[dict(identity=('new',i)) for i in range(3)]
        class Guidance:
            def __init__(self,a,g,b,st,seq,mask,free,fm,*args):
                self.a=a;self.seq=seq;self.mask=mask;self.free=free;self.free_mask=fm;self.version=0;self.calls=0
            def remember_search(self,*args):pass
            def finish_chunk(self,*args):pass
            def annotate(self,*args):pass
            def mark_attempted(self,*args):pass
            def report(self):return {}
            def refine(self,*args):
                self.calls+=1
                values=self.a.step([1,1],[1])[2];offset=self.free_mask.bit_length()
                self.free=[v|(bit<<offset) for v,bit in zip(self.free,values)];self.free_mask=(1<<(offset+1))-1
                return [dict(root=5)] if union and self.calls==1 else []
        def search(s,root,pool,info,seq,sm,free,fm,*args):
            searches.append((fm.bit_length(),tuple(free)));return [dict(root=root)],{}
        def prove(a,g,maps,free,candidates,*args,**kwargs):
            proof_widths.append(tuple(free))
            n=len(proof_widths)
            return ((old if n==1 else new if n==2 else []) if union else []),{}
        with patch.object(im,'InlineImageGuidance',Guidance),patch.object(at,'search_root',side_effect=search),\
             patch.object(at,'prove_chunk',side_effect=prove),patch.object(at,'emit'),\
             patch.object(at,'publish_checkpoint',side_effect=lambda source,qualified,*a,**k:published.append(copy.deepcopy(qualified))):
            at.transform(job)
        return searches,proof_widths,published

    def test_empty_free_only_result_still_updates_later_search_and_proof(self):
        searches,widths,_=self.run_mocked()
        self.assertEqual([x[0] for x in searches],[256,257]);self.assertEqual(widths,[x[1] for x in searches])

    def test_established_qualified_union_is_never_replaced_by_new_topk(self):
        _,_,published=self.run_mocked(union=True)
        self.assertEqual([len(x) for x in published],[0,49,52])
        self.assertEqual(len({c['identity'] for c in published[-1]}),52)

@unittest.skipUnless(SOLVER,'requires STRAN2_INLINE_SOLVER')
class AuthenticatedBridgeTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.out=Path(self.tmp.name)
        self.path,self.a,self.g,self.maps,_,_,self.c=fixture(self.out,same_next=False)
        self.solver=Path(SOLVER);self.identity,self.solver_hash=at.bind_executable(self.solver)
        self.mask=(1<<256)-1
        # One duplicated original-graph free witness; source model predecessors
        # necessarily use previous PI[1,0], distinct from this initial PI[1,1].
        values=self.a.step([1,1],[1,0])[2];self.free=[v*self.mask for v in values];self.c['witness_lane']=0
        # Complete image worlds make every source image projection redundant,
        # while the intentionally restricted free lanes can still grow.
        samples=[]
        for world in range(16):
            current=[(world>>i)&1 for i in range(2)]
            previous=[(world>>(i+2))&1 for i in range(2)]
            successor=self.a.step(previous,[0,0])[1]
            samples.append(self.a.step(current,successor)[2])
        self.seq=[sum(v[node]<<i for i,v in enumerate(samples)) for node in range(self.a.m+1)]
        self.seqmask=(1<<len(samples))-1
        self.job=dict(case=dict(input=str(self.path),input_sha256=p.sha(self.path)),out=str(self.out),
            source_hashes={'test':'f'*64},solver_sha256=self.solver_hash,inline_image_models=True,predecessor_free=True,chunk_roots=32)
        self.context=dict(input_sha256=p.sha(self.path),source_hashes=self.job['source_hashes'],solver_sha256=self.solver_hash)

    def prove(self,candidates=None,chunk=0):
        cs=[copy.deepcopy(self.c)] if candidates is None else candidates
        at.prove_chunk(self.a,self.g,self.maps,self.free,cs,self.out/'chunks'/f'chunk_{chunk:05d}',
            self.solver,budget(),p.sha(self.path),self.identity,inline_model_context=self.context)
        return cs

    def guidance(self,cone=False):
        job=dict(self.job,inline_cone_check=cone)
        return im.InlineImageGuidance(self.a,self.g,self.maps['free'],self.maps['step'],self.seq,self.seqmask,self.free,self.mask,
                                      p.Structure(self.a),p.Config(),job,budget(),None)

    def collect(self,candidates,cone=False,tag='collection'):
        target=self.out/tag
        _,report=im.collect_inline_models(self.a,self.g,self.maps['free'],self.maps['step'],candidates,target,
                                        dict(self.job,inline_cone_check=cone),budget(),{})
        return target,report,json.loads((target/'replayed_models.json').read_text())

    def test_authenticated_free_only_progress_with_no_duplicate_solver(self):
        cs=self.prove();guide=self.guidance();roots=[dict(root=7,pool=[1,2,3,4,5,6],pool_info={})]
        guide.remember_search(7,roots[0]['pool'],{},[],{});guide.mark_attempted(cs)
        before=list(guide.seq);version=guide.version
        with patch.object(im.subprocess,'run',side_effect=AssertionError('duplicate solve')),patch.object(p,'search_root',return_value=([],{})) as search:
            self.assertEqual(guide.refine(roots,cs,self.out),[])
        self.assertEqual(guide.seq,before);self.assertEqual(guide.version,version)
        self.assertGreater(guide.free_mask.bit_length(),256);self.assertEqual(search.call_count,1)
        self.assertEqual(guide.report()['free_only_search_rounds'],1)
        self.assertEqual(len(guide.attempted),1)

    def test_actual_free_only_cap_retains_second_authenticated_world(self):
        first=self.prove()
        # A second genuine image countermodel requires previous PI[0,1],
        # unlike the first source's[1,0]. Both image rows are already covered.
        alternative=dict(root=7,recipe=[12,2],out=-2,witness_lane=0,
                         **p.Structure(self.a).cost(7,[12,2],-2))
        values=self.a.step([1,1],[0,1])[2];other_free=[v*self.mask for v in values]
        second=[alternative]
        at.prove_chunk(self.a,self.g,self.maps,other_free,second,self.out/'chunks/chunk_00001',
            self.solver,budget(),p.sha(self.path),self.identity,inline_model_context=self.context)
        guide=self.guidance();roots=[dict(root=7,pool=[1,2,3,4,5,6],pool_info={})]
        guide.remember_search(7,roots[0]['pool'],{},[],{});guide.mark_attempted(first)
        with patch.object(im.subprocess,'run',side_effect=AssertionError('duplicate solve')),patch.object(p,'search_root',return_value=([],{})) as search:
            guide.refine(roots,first,self.out)
            guide.mark_attempted(second)
            guide.refine(roots,second,self.out)
        self.assertEqual(search.call_count,1)
        self.assertEqual(guide.free_mask.bit_length(),258)
        self.assertEqual(guide.free_guidance.state.snapshot().records[-1].inputs,(0,1))
        report=json.loads((self.out/'image_guidance/round_00001/refinement.json').read_text())
        self.assertEqual(report['stopping_reason'],'FREE_ONLY_REVISIT_CAP')
        self.assertEqual(report['free_admission']['added'],1)
        self.assertEqual(report['discovery_executed_roots'],0)
        guide.finish_chunk(roots)
        self.assertFalse(guide.search_cache)
        self.assertEqual(guide.free_mask.bit_length(),258)

    def test_source_receipt_cache_reuse_preserves_raw_model_row(self):
        other=dict(self.c,recipe=list(reversed(self.c['recipe'])))
        cs=self.prove([copy.deepcopy(self.c),other]);guide=self.guidance();target,report,rows=self.collect(cs)
        self.assertTrue(cs[1]['anytime_certificate']['receipts']['step']['reused'])
        self.assertEqual(cs[0]['anytime_certificate']['receipts']['step']['inline_image_model'],
                         cs[1]['anytime_certificate']['receipts']['step']['inline_image_model'])
        result=guide.free_guidance.admit(cs,target,report,rows)
        self.assertEqual(result['added'],1)
        self.assertEqual(result['decisions'][1]['action'],'EXACT_FREE_WORLD_DUPLICATE')
        record=guide.free_guidance.state.snapshot().records[0];origin=json.loads(record.provenance_json)
        self.assertEqual(origin['model_manifest']['model_row'],record.source_model_index)

    def test_tampered_receipt_or_raw_assignment_rejects_before_append(self):
        cs=self.prove();guide=self.guidance();target,report,rows=self.collect(cs);before=guide.free_guidance.state.snapshot()
        rows[0]['previous_inputs'][0]^=1
        with self.assertRaisesRegex(ValueError,'authenticated raw'):
            guide.free_guidance.admit(cs,target,report,rows)
        self.assertIs(guide.free_guidance.state.snapshot(),before)

    def test_cone_binding_is_mandatory_when_enabled(self):
        cs=self.prove();guide=self.guidance(cone=True);target,report,rows=self.collect(cs,cone=True)
        bad=dict(report);bad.pop('compiled_model_validator')
        with self.assertRaisesRegex(ValueError,'cone-validator'):
            guide.free_guidance.admit(cs,target,bad,rows)
        self.assertEqual(guide.free_guidance.admit(cs,target,report,rows)['added'],1)

    def test_deadline_after_admission_cannot_publish_a_new_manifest(self):
        cs=self.prove();guide=self.guidance();target,report,rows=self.collect(cs)
        helper=guide.free_guidance;original=helper.state.append_verified_models
        def expire(*args):
            result=original(*args);helper.deadline.end=0;return result
        with patch.object(helper.state,'append_verified_models',side_effect=expire):
            with self.assertRaises(TimeoutError):helper.admit(cs,target,report,rows)
        self.assertEqual(sorted(p.name for p in (self.out/'free_domains').iterdir()),['version_00000.json'])

    def test_full_free_reconstruction_and_old_discovery_version(self):
        cs=self.prove();guide=self.guidance();helper=guide.free_guidance
        old=copy.deepcopy(self.c);helper.annotate([old])
        target,report,rows=self.collect(cs);helper.admit(cs,target,report,rows)
        current=copy.deepcopy(self.c);helper.annotate([current])
        self.assertEqual(old['free_domain']['manifest']['free_version'],0)
        self.assertEqual(current['free_domain']['manifest']['free_version'],1)
        for c in (old,current):
            free,manifest=fg.reconstruct_free_manifest(self.a,self.out,c['free_domain']['manifest'],p.sha(self.path),self.free)
            ordinary=p.witness(self.a,c,free)
            fg.verify_witness_annotation(self.a,c,ordinary,self.out,p.sha(self.path))
        self.assertEqual(tuple(free),helper.state.snapshot().signatures)

    def test_tampered_free_hash_origin_and_unused_appended_lane_reject(self):
        cs=self.prove();guide=self.guidance();helper=guide.free_guidance;target,report,rows=self.collect(cs)
        helper.admit(cs,target,report,rows);selected=copy.deepcopy(self.c);helper.annotate([selected])
        self.assertEqual(selected['witness_lane'],0)  # appended lane256 is unused by this witness
        reference=selected['free_domain']['manifest'];path=self.out/'free_domains'/reference['file']
        original=json.loads(path.read_text())
        for kind in ('domain_hash','origin','unused_lane'):
            changed=copy.deepcopy(original);bound=copy.deepcopy(reference)
            if kind=='domain_hash':
                changed['free_domain_sha256']='0'*64;bound['free_domain_sha256']='0'*64
            elif kind=='origin':
                origin=json.loads(changed['records'][0]['provenance_json']);origin['input_sha256']='0'*64
                changed['records'][0]['provenance_json']=json.dumps(origin)
            else:changed['records'][0]['inputs'][0]^=1
            p.write_json(path,changed);bound['sha256']=p.sha(path)
            with self.assertRaises(ValueError):fg.reconstruct_free_manifest(self.a,self.out,bound,p.sha(self.path),self.free)
        p.write_json(path,original)

    def test_selected_appended_origin_audit_authenticates_without_solver(self):
        import sys
        from pathlib import Path
        sys.path.insert(0,str(Path(ig.__file__).resolve().parents[1]/'image_cegar_diagnostic'))
        import audit_online_products as audit
        cs=self.prove();guide=self.guidance();helper=guide.free_guidance;target,report,rows=self.collect(cs)
        helper.admit(cs,target,report,rows);snap=helper.state.snapshot()
        c=dict(root=7,recipe=[2,13],out=-2,witness_lane=256,**p.Structure(self.a).cost(7,[2,13],-2))
        helper.annotate([c]);c['free_witness']=p.witness(self.a,c,snap.signatures)
        out=self.out/'audit';out.mkdir();bound={}
        with patch.object(im.subprocess,'run',side_effect=AssertionError('audit re-solved model')):
            result=audit.validate_appended_free_witnesses(p,self.a,p.Structure(self.a),self.free,self.g,
                self.maps['free'],self.maps['step'],[c],self.out,self.job,out,bound)
        self.assertEqual(result['selected_appended_witnesses'],1)
        self.assertEqual(result['authenticated_distinct_source_models'],1)
        self.assertTrue(any(name.endswith('.models.jsonl') for name in bound))
        missing=copy.deepcopy(c);del missing['free_domain']
        with self.assertRaisesRegex(ValueError,'lost free provenance'):
            audit.validate_appended_free_witnesses(p,self.a,p.Structure(self.a),self.free,self.g,
                self.maps['free'],self.maps['step'],[missing],self.out,self.job,out,bound)

    def test_annotation_survives_ordinary_witness_replay_and_detects_tamper(self):
        cs=self.prove();guide=self.guidance();target,report,rows=self.collect(cs);helper=guide.free_guidance
        helper.admit(cs,target,report,rows);snap=helper.state.snapshot()
        # Any original candidate with an actual difference on the saved lane is
        # sufficient for provenance plumbing; no new Build-quality claim.
        lane=256;values=[(x>>lane)&1 for x in snap.signatures]
        output=1-values[7];candidate=dict(root=7,recipe=[],out=output,witness_lane=lane)
        helper.annotate([candidate]);ordinary=p.witness(self.a,candidate,snap.signatures)
        fg.verify_witness_annotation(self.a,candidate,ordinary,self.out,p.sha(self.path))
        candidate['free_domain']['witness']['lane']=0
        with self.assertRaises(ValueError):fg.verify_witness_annotation(self.a,candidate,ordinary,self.out,p.sha(self.path))

if __name__=='__main__':unittest.main()
