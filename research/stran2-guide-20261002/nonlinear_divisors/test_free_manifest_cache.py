"""IO-cache adversaries; no performance conclusions from these tests."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import anytime as at
import free_guided as fg
import prototype as p
from free_manifest_cache import ManifestCache
from test_anytime import budget,fixture,rewrite_preserving_mtime_with_changed_ctime

class CacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.out=Path(self.tmp.name);(self.out/'free_domains').mkdir();self.clock=budget()
        self.cache=ManifestCache(self.out,'a'*64,(1,1),self.clock);self.addCleanup(self.cache.close)

    def add(self,version):
        records=[dict(lane=256+i,domain='unrestricted_free_PI_RO',sampled_pi_field='previous_inputs',
                      inputs=[i%2],state=[(i//2)%2],provenance_json=json.dumps(dict(input_sha256='a'*64)))for i in range(version)]
        payload=dict(schema=1,domain='unrestricted_free_PI_RO',input_sha256='a'*64,free_version=version,
                     free_domain_sha256=f'{version:064x}',initial_domain_sha256='b'*64,free_signature_bits=256+version,
                     free_mask=hex((1<<(256+version))-1),initial_lanes=256,global_added_cap=256,
                     sampled_pi_field='previous_inputs',initial_ci_signatures=['0x1','0x2'],records=records)
        path=self.out/'free_domains'/f'version_{version:05d}.json';p.write_json(path,payload)
        bound=dict(file=path.name,sha256=p.sha(path),free_version=version,free_domain_sha256=payload['free_domain_sha256'],
                   free_signature_bits=256+version)
        self.cache.register(bound,payload);return bound,path,payload

    def test_immutable_payload_and_caller_reference_are_not_aliased(self):
        bound,_,payload=self.add(1);saved=copy.deepcopy(bound);payload['records'][0]['inputs'][0]=1;bound['sha256']='c'*64
        with self.cache.witness_payload(saved) as frozen:
            self.assertEqual(frozen['records'][0]['inputs'],(0,))
            with self.assertRaises(TypeError):frozen['records'][0]['inputs'][0]=1
            with self.assertRaises(TypeError):frozen['free_version']=2
        with self.assertRaisesRegex(ValueError,'reference changed'):self.cache.check_identity(bound)
        self.assertEqual(len(self.cache.entries),0)

    def test_two_descriptors_close_on_eviction_reload_and_final(self):
        refs=[self.add(i)[0]for i in range(4)]
        self.assertEqual(len(self.cache.entries),2)
        before=self.cache.metrics['payload_parses'];self.cache.authenticate([refs[0]])
        self.assertGreater(self.cache.metrics['payload_parses'],before)
        self.cache.verify_all();self.assertEqual(self.cache.metrics['peak_open_descriptors'],2)
        self.assertEqual(len(self.cache.identities),4);self.cache.close()
        self.assertEqual(self.cache.metrics['descriptor_opens'],self.cache.metrics['descriptor_closes'])

    def test_changed_same_size_restored_mtime_rejected(self):
        bound,path,_=self.add(0);data=path.read_bytes()
        rewrite_preserving_mtime_with_changed_ctime(path,data.replace(b'0x1',b'0x3'))
        with self.assertRaisesRegex(ValueError,'identity changed'):self.cache.check_identity(bound)
        self.assertTrue(self.cache.closed);self.assertFalse(self.cache.entries)

    def test_identical_byte_inode_replacement_rejected(self):
        bound,path,_=self.add(0);replacement=self.out/'replacement';replacement.write_bytes(path.read_bytes());replacement.replace(path)
        with self.assertRaisesRegex(ValueError,'identity changed'):self.cache.authenticate([bound])

    def test_symlink_and_parent_directory_replacement_rejected(self):
        bound,path,_=self.add(0);old=self.out/'old';(self.out/'free_domains').rename(old)
        (self.out/'free_domains').mkdir();os.link(old/path.name,path)
        with self.assertRaisesRegex(ValueError,'directory identity changed'):self.cache.authenticate([bound])

    def test_leaf_symlink_rejected(self):
        bound,path,_=self.add(0);other=self.out/'other';path.rename(other);path.symlink_to(other)
        with self.assertRaisesRegex(ValueError,'identity changed'):self.cache.authenticate([bound])

    def test_mutation_during_witness_context_closes_every_descriptor(self):
        bound,path,_=self.add(0);self.add(1)
        with self.assertRaisesRegex(ValueError,'identity changed'):
            with self.cache.witness_payload(bound):path.write_bytes(path.read_bytes()+b' ')
        self.assertTrue(self.cache.closed);self.assertEqual(len(self.cache.entries),0)

    def test_unrelated_version_does_not_mask_evicted_file_final_failure(self):
        old,path,_=self.add(0);self.add(1);current,_,_=self.add(2)
        path.write_bytes(path.read_bytes()+b' ')
        self.cache.authenticate([current])  # Does not consume the old version.
        with self.assertRaisesRegex(ValueError,'identity changed'):self.cache.verify_all()

    def test_full_entry_exit_hashes_are_not_replaced_by_stat_checks(self):
        bound,path,_=self.add(0);candidate=dict(free_domain=dict(manifest=bound))
        with patch.object(self.cache,'_check'):
            with self.assertRaisesRegex(ValueError,'full content hash changed'):
                with self.cache.proof_boundary([candidate]):path.write_bytes(path.read_bytes().replace(b'0x1',b'0x3'))
        self.assertTrue(self.cache.closed)

    def test_same_version_different_domain_rejected(self):
        bound,_,_=self.add(0);wrong=dict(bound,free_domain_sha256='e'*64)
        with self.assertRaisesRegex(ValueError,'reference changed'):self.cache.authenticate([wrong])

    def test_deadline_failure_closes_cached_descriptors(self):
        bound,_,_=self.add(0);self.add(1)
        with patch.object(self.clock,'remaining',side_effect=TimeoutError('injected deadline')):
            with self.assertRaises(TimeoutError):self.cache.authenticate([bound])
        self.assertFalse(self.cache.entries)

    def test_creation_rejects_replaced_directory_before_write(self):
        self.add(0);(self.out/'free_domains').rename(self.out/'old');(self.out/'free_domains').mkdir()
        with self.assertRaisesRegex(ValueError,'directory identity changed'):
            self.cache.check_creation_destination('version_00001.json')
        self.assertEqual(list((self.out/'free_domains').iterdir()),[])

    def test_exclusive_publication_matches_original_json_bytes(self):
        _,_,payload=self.add(0);payload['free_version']=1
        expected=self.out/'expected';p.write_json(expected,payload)
        self.cache.write_new('version_00001.json',payload)
        self.assertEqual((self.out/'free_domains/version_00001.json').read_bytes(),expected.read_bytes())
        self.assertFalse((self.out/'free_domains/version_00001.json.tmp').exists())
        self.cache.close();self.assertEqual(self.cache.metrics['descriptor_opens'],self.cache.metrics['descriptor_closes'])
        self.assertLessEqual(self.cache.metrics['peak_open_descriptors'],2)

    def test_target_race_cannot_overwrite_existing_version(self):
        _,_,payload=self.add(0);name='version_00001.json';target=self.out/'free_domains'/name
        original=os.link
        def race(*args,**kwargs):target.write_bytes(b'preserve competitor');return original(*args,**kwargs)
        with patch('free_manifest_cache.os.link',side_effect=race):
            with self.assertRaises(FileExistsError):self.cache.write_new(name,payload)
        self.assertEqual(target.read_bytes(),b'preserve competitor');self.assertTrue(self.cache.closed)
        self.assertEqual(self.cache.metrics['descriptor_opens'],self.cache.metrics['descriptor_closes'])

    def test_temp_symlink_race_cannot_write_through(self):
        _,_,payload=self.add(0);name='version_00001.json';victim=self.out/'victim';victim.write_bytes(b'untouched')
        original=os.open
        def race(path,*args,**kwargs):
            if path==name+'.tmp':(self.out/'free_domains'/path).symlink_to(victim)
            return original(path,*args,**kwargs)
        with patch('free_manifest_cache.os.open',side_effect=race):
            with self.assertRaises(FileExistsError):self.cache.write_new(name,payload)
        self.assertEqual(victim.read_bytes(),b'untouched');self.assertFalse((self.out/'free_domains'/name).exists())
        self.assertEqual(self.cache.metrics['descriptor_opens'],self.cache.metrics['descriptor_closes'])

    def test_temp_substitution_during_link_uses_descriptor_and_rejects(self):
        _,_,payload=self.add(0);name='version_00001.json';victim=self.out/'victim';victim.write_bytes(b'untouched')
        original=os.link
        def race(*args,**kwargs):
            temp=self.out/'free_domains'/(name+'.tmp');temp.unlink();temp.symlink_to(victim)
            return original(*args,**kwargs)
        with patch('free_manifest_cache.os.link',side_effect=race):
            # Linux may reject linking an already-unlinked open inode before
            # our post-link identity check. Both outcomes fail closed.
            with self.assertRaises((ValueError,FileNotFoundError)):self.cache.write_new(name,payload)
        self.assertEqual(victim.read_bytes(),b'untouched');self.assertTrue(self.cache.closed)
        self.assertEqual(self.cache.metrics['descriptor_opens'],self.cache.metrics['descriptor_closes'])

    def test_parent_substitution_during_write_never_writes_replacement_dir(self):
        _,_,payload=self.add(0);original=os.write;changed=False
        def race(*args,**kwargs):
            nonlocal changed
            if not changed:
                changed=True;(self.out/'free_domains').rename(self.out/'old');(self.out/'free_domains').mkdir()
            return original(*args,**kwargs)
        with patch('free_manifest_cache.os.write',side_effect=race):
            with self.assertRaisesRegex(ValueError,'directory identity changed'):self.cache.write_new('version_00001.json',payload)
        self.assertEqual(list((self.out/'free_domains').iterdir()),[])
        self.assertEqual(self.cache.metrics['descriptor_opens'],self.cache.metrics['descriptor_closes'])


class RuntimeCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.out=Path(self.tmp.name)
        self.path,self.a,self.graph,self.maps,_,_,self.c=fixture(self.out)
        self.cfg=p.Config();(self.free,_,_),self.mask=p.signatures(self.graph,[self.maps['free'],self.maps['step'],self.maps['reset']],self.cfg)
        difference=p.recipe_eval(self.c['recipe'],self.c['out'],self.free,self.mask)^self.free[self.c['root']]
        self.c['witness_lane']=(difference&-difference).bit_length()-1
        self.job=dict(case=dict(input=str(self.path),input_sha256=p.sha(self.path)),out=str(self.out),
                      predecessor_free=True,inline_image_models=True,free_manifest_cache=True,chunk_roots=32)
        p.write_json(self.out/'job.json',self.job);self.clock=budget()
        self.helper=fg.PredecessorFreeDomain(self.a,self.graph,self.maps['free'],self.maps['step'],self.free,self.mask,self.job,self.cfg,self.clock)
        self.cache=self.helper.manifest_cache;self.addCleanup(self.cache.close)

    def test_empty_annotation_has_no_io_but_later_consumption_rejects(self):
        path=self.out/'free_domains/version_00000.json';path.write_bytes(path.read_bytes()+b' ')
        before=dict(self.cache.metrics);self.helper.annotate([]);self.assertEqual(dict(self.cache.metrics),before)
        with self.assertRaisesRegex(ValueError,'identity changed'):self.helper.annotate([self.c])

    def test_cached_and_old_full_witness_verification_agree(self):
        self.helper.annotate([self.c]);w=p.witness(self.a,self.c,self.free)
        old=fg.verify_witness_annotation(self.a,self.c,w,self.out,p.sha(self.path))
        with self.cache.proof_boundary([self.c]):
            new=fg.verify_witness_annotation(self.a,self.c,w,self.out,p.sha(self.path),self.cache)
        self.assertEqual(old,new)
        self.cache.verify_all()

    def test_annotation_still_replays_original_aig(self):
        with patch.object(fg.fs.FrozenOriginalAig,'values',side_effect=ValueError('replay invoked')):
            with self.assertRaisesRegex(ValueError,'replay invoked'):self.helper.annotate([self.c])
        self.assertTrue(self.cache.closed)

    def test_wrong_input_context_rejected(self):
        self.helper.annotate([self.c]);w=p.witness(self.a,self.c,self.free)
        with self.assertRaisesRegex(ValueError,'context differs'):
            fg.verify_witness_annotation(self.a,self.c,w,self.out,'f'*64,self.cache)
        self.assertFalse(self.cache.entries)

    def test_malformed_annotation_closes_descriptors_before_lookup(self):
        self.helper.annotate([self.c]);self.c['free_domain']['policy']='wrong'
        with self.assertRaisesRegex(ValueError,'policy'):
            fg.verify_witness_annotation(self.a,self.c,p.witness(self.a,self.c,self.free),self.out,p.sha(self.path),self.cache)
        self.assertFalse(self.cache.entries)

    def test_empty_annotation_deadline_closes_all(self):
        with patch.object(self.clock,'remaining',side_effect=TimeoutError('injected')):
            with self.assertRaises(TimeoutError):self.helper.annotate([])
        self.assertFalse(self.cache.entries)

    def test_worker_and_cli_mode_prerequisite(self):
        job=dict(case={},config=vars(self.cfg),chunk_roots=32,free_manifest_cache=True)
        with self.assertRaisesRegex(ValueError,'requires predecessor-free'):at.transform(job)

    def prove(self):
        self.helper.annotate([self.c]);solver=Path(os.environ['STRAN2_INLINE_SOLVER']);identity,_=at.bind_executable(solver)
        qualified,_=at.prove_chunk(self.a,self.graph,self.maps,self.free,[self.c],self.out/'chunks/chunk_00000',solver,self.clock,
                                  p.sha(self.path),identity,free_domain_required=True,free_manifest_cache=self.cache)
        self.assertEqual(qualified,[self.c]);return qualified

    @unittest.skipUnless(os.environ.get('STRAN2_INLINE_SOLVER'),'requires STRAN2_INLINE_SOLVER')
    def test_mutation_just_before_checkpoint_notice_is_not_published(self):
        qualified=self.prove();original=at.create_product;path=self.out/'free_domains/version_00000.json'
        def mutate(*args,**kwargs):
            result=original(*args,**kwargs);path.write_bytes(path.read_bytes()+b' ');return result
        with patch.object(at,'create_product',side_effect=mutate),patch.object(at,'emit') as emit:
            with self.assertRaisesRegex(ValueError,'identity changed'):
                at.publish_checkpoint(self.path,qualified,self.out,0,self.clock,p.sha(self.path),{},self.cache)
            emit.assert_not_called()
        self.assertTrue(self.cache.closed)

    @unittest.skipUnless(os.environ.get('STRAN2_INLINE_SOLVER'),'requires STRAN2_INLINE_SOLVER')
    def test_prior_checkpoint_ignores_unreferenced_later_mutation_until_final(self):
        qualified=self.prove();events=[]
        with patch.object(at,'emit',side_effect=events.append):
            at.publish_checkpoint(self.path,qualified,self.out,0,self.clock,p.sha(self.path),{},self.cache)
        original=events[0];old=copy.deepcopy(self.helper.manifests[0]);payload=json.loads((self.out/'free_domains'/old['file']).read_text())
        # An extra metadata fixture version, not a new domain/search experiment.
        payload['free_version']=1;path=self.out/'free_domains/version_00001.json';p.write_json(path,payload)
        later=dict(old,file=path.name,free_version=1,sha256=p.sha(path));self.cache.register(later,payload)
        path.write_bytes(path.read_bytes()+b' ')
        # The old selected set references only version0; its boundary and the
        # unchanged independent verifier remain valid.
        with patch.object(at,'emit',side_effect=events.append):
            at.publish_checkpoint(self.path,qualified,self.out,1,self.clock,p.sha(self.path),{},self.cache)
        at.verify_checkpoint(self.out,original,p.sha(self.path),free_domain_required=True)
        with self.assertRaisesRegex(ValueError,'identity changed'):self.cache.verify_all()
        self.assertEqual(len(events),2)

    def test_transform_finally_closes_resources_on_error(self):
        def fail(job,resources):resources.append(self.cache);raise TimeoutError('worker deadline')
        with patch.object(at,'_transform',side_effect=fail):
            with self.assertRaises(TimeoutError):at.transform({})
        self.assertFalse(self.cache.entries)

    @unittest.skipUnless(os.environ.get('STRAN2_INLINE_SOLVER'),'requires STRAN2_INLINE_SOLVER')
    def test_mutation_during_solver_withholds_entire_chunk(self):
        self.helper.annotate([self.c]);solver=Path(os.environ['STRAN2_INLINE_SOLVER']);identity,_=at.bind_executable(solver)
        original=at.FrozenQueries.solve;path=self.out/'free_domains/version_00000.json'
        def mutate(broker,requests,phase):
            result=original(broker,requests,phase)
            if phase=='step':path.write_bytes(path.read_bytes()+b' ')
            return result
        with patch.object(at.FrozenQueries,'solve',new=mutate):
            with self.assertRaisesRegex(ValueError,'identity changed'):
                at.prove_chunk(self.a,self.graph,self.maps,self.free,[self.c],self.out/'chunks/chunk_00000',solver,self.clock,
                               p.sha(self.path),identity,free_domain_required=True,free_manifest_cache=self.cache)
        self.assertTrue(self.cache.closed);self.assertFalse((self.out/'checkpoints').exists())


@unittest.skipUnless(os.environ.get('STRAN2_INLINE_SOLVER'),'requires STRAN2_INLINE_SOLVER')
class RealAppendedVersionTests(unittest.TestCase):
    def test_authenticated_original_predecessor_append_with_cache(self):
        from test_free_guided import AuthenticatedBridgeTests
        base=AuthenticatedBridgeTests();base.setUp();self.addCleanup(base.doCleanups)
        base.job['free_manifest_cache']=True
        candidates=base.prove();guide=base.guidance();helper=guide.free_guidance;self.addCleanup(helper.manifest_cache.close)
        target,report,rows=base.collect(candidates);admission=helper.admit(candidates,target,report,rows)
        self.assertGreater(admission['added'],0)
        self.assertEqual(helper.state.snapshot().version,1)
        bound=helper.manifests[1];saved=json.loads((base.out/'free_domains'/bound['file']).read_text())
        self.assertTrue(saved['records']);self.assertIsInstance(helper.state.snapshot().records[0].inputs,tuple)
        with helper.manifest_cache.witness_payload(bound) as cached:
            self.assertEqual(tuple(saved['records'][0]['inputs']),cached['records'][0]['inputs'])
        helper.manifest_cache.verify_all()


if __name__=='__main__':unittest.main()
