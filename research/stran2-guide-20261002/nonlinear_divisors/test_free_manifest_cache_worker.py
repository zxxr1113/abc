"""Tiny functional workers and supervisor timeout; never a performance pilot."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

import anytime as at
import image_guided as ig
import inline_models as im
import free_guided as fg
import free_manifest_cache as mc
import prototype as p
from product import write_aig

SOLVER=os.environ.get('STRAN2_INLINE_SOLVER')
OLD_SOURCE=os.environ.get('STRAN2_PRE_CACHE_SOURCE')

@unittest.skipUnless(SOLVER,'requires STRAN2_INLINE_SOLVER')
class WorkerTests(unittest.TestCase):
    def setUp(self):
        preserve=os.environ.get('STRAN2_CACHE_WORKER_FIXTURE_OUT')
        if preserve:
            self.out=Path(preserve)/self._testMethodName;self.out.mkdir(parents=True,exist_ok=False)
        else:
            temporary=tempfile.TemporaryDirectory();self.addCleanup(temporary.cleanup);self.out=Path(temporary.name)
        self.input=self.out/'common/inputs/first_seq/tiny.aig';self.input.parent.mkdir(parents=True)
        write_aig(self.input,dict(ni=2,nl=2,gates=[(2,6),(4,8),(10,12)],outputs=[14],latches=[2,2]))
        loaded=self.out/'common/inputs/loaded/tiny.aig';loaded.parent.mkdir();shutil.copyfile(self.input,loaded)
        self.case=dict(file='tiny.aig',family='synthetic',first_seq_path=str(self.input),first_seq_sha256=p.sha(self.input),
                       loaded_path=str(loaded),loaded_sha256=p.sha(loaded),loaded_AND=3,input=str(self.input),input_sha256=p.sha(self.input))
        self.solver=Path(SOLVER);self.identity,self.solver_hash=at.bind_executable(self.solver)

    def package(self,source,name):
        target=self.out/name;target.mkdir()
        for folder in ('nonlinear_divisors','image_cegar_diagnostic','free_domain_diagnostic','seq_cut_image',
                       'seq_care_synthesis','teacher_adaptive_tools'):
            (target/folder).mkdir()
            for path in (source/folder).iterdir():
                if path.is_file()and path.suffix in ('.py','.c','.sh'):shutil.copyfile(path,target/folder/path.name)
        p.write_json(target/'cases.json',dict(cases=[self.case]));return target

    @unittest.skipUnless(OLD_SOURCE,'requires STRAN2_PRE_CACHE_SOURCE')
    def test_actual_cli_default_matches_precache_and_optin_products(self):
        old=self.package(Path(OLD_SOURCE),'old-package');new=self.package(p.PACKAGE,'new-package');outputs={}
        for mode,source,flag in [('precache',old,False),('default',new,False),('cache',new,True)]:
            run=self.out/mode
            command=[sys.executable,'-B',str(source/'nonlinear_divisors/anytime.py'),'--case','tiny.aig','--out',str(run),
                     '--solver',str(self.solver),'--inline-image-models','--predecessor-free','--workers','1','--wall-seconds','30']
            if flag:command+=['--free-manifest-cache']
            result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
            (self.out/(mode+'.log')).write_text(result.stdout);p.write_json(self.out/(mode+'.command.json'),command)
            self.assertEqual(result.returncode,0,result.stdout)
            record=json.loads((run/'tiny/result.json').read_text());self.assertEqual(record['status'],'COMPLETE')
            run_plan=json.loads((run/'plan.json').read_text());job=json.loads((run/'tiny/job.json').read_text())
            self.assertEqual(json.loads((run/'source_integrity.json').read_text())['status'],'PASS')
            self.assertEqual(job['source_hashes'],run_plan['runtime_source_hashes'])
            for name,h in run_plan['runtime_source_hashes'].items():
                self.assertEqual(p.sha(run/'source'/name),h);self.assertEqual(p.sha(source/name),h)
            checkpoint=Path(record['selected_checkpoint']['directory']);selected=json.loads((checkpoint/'selection.json').read_text())['selected']
            self.assertTrue(selected)
            outputs[mode]=dict(product=(checkpoint/'product.aig').read_bytes(),without=(checkpoint/'replay_without_build.aig').read_bytes(),
                roots=(run/'tiny/root_search.jsonl').read_bytes(),selected=[{k:c[k]for k in ('root','recipe','out','free_witness','free_domain','proof')}for c in selected],
                proof_files={str(path.relative_to(run/'tiny')):path.read_bytes()for pattern in ('*.cnf','*.queries')
                             for path in (run/'tiny/chunks').rglob(pattern)})
            if flag:
                report=json.loads((run/'tiny/free_manifest_cache.json').read_text());self.assertTrue(report['all_created_verified'])
                self.assertTrue(report['closed']);self.assertEqual(report['open_descriptors'],0)
                self.assertLessEqual(report['metrics']['peak_open_descriptors'],2)
            else:
                self.assertNotIn('free_manifest_cache',json.loads((run/'plan.json').read_text()))
                self.assertFalse((run/'tiny/free_manifest_cache.json').exists())
                self.assertFalse((run/'source/nonlinear_divisors/free_manifest_cache.py').exists())
        self.assertEqual(outputs['precache'],outputs['default'])
        self.assertEqual(outputs['default'],outputs['cache'])
        old_plan=json.loads((self.out/'precache/plan.json').read_text());default_plan=json.loads((self.out/'default/plan.json').read_text())
        self.assertEqual(set(old_plan['runtime_source_hashes']),set(default_plan['runtime_source_hashes']))
        p.write_json(self.out/'result.json',dict(status='PASS',default_old_artifacts_identical=True,
            optin_products_witnesses_roots_and_queries_identical=True,tiny_functional_fixture=True,performance_comparison='NOT_RUN'))

    def test_hard_timeout_after_checkpoint_and_separate_external_verification(self):
        out=self.out/'worker';out.mkdir();(out/'chunks').mkdir()
        runtime=list(dict.fromkeys(at.RUNTIME+ig.RUNTIME+im.RUNTIME+fg.RUNTIME+mc.RUNTIME))
        start=time.monotonic();seconds=2.0
        job=dict(case=self.case,config=vars(p.Config(wall_seconds=seconds)),out=str(out),solver=str(self.solver),
                 solver_sha256=self.solver_hash,solver_identity=self.identity,start=start,end=start+seconds,
                 chunk_roots=32,source_hashes={name:p.sha(p.PACKAGE/name)for name in runtime},
                 inline_image_models=True,predecessor_free=True,free_manifest_cache=True)
        job_path=out/'job.json';p.write_json(job_path,job);marker=out/'final_guard_entered.json'
        code=f'''import sys,time,json,os
from pathlib import Path
sys.path.insert(0,{str(p.PACKAGE/'nonlinear_divisors')!r})
import anytime as at
import free_manifest_cache as mc
original=mc.ManifestCache.verify_all
def stop_after_guard(self):
 original(self)
 Path({str(marker)!r}).write_text(json.dumps(dict(pid=os.getpid(),report=self.report())))
 time.sleep(30)
mc.ManifestCache.verify_all=stop_after_guard
raise SystemExit(at.worker({str(job_path)!r}))
'''
        driver=at.supervise([sys.executable,'-B','-c',code],out,start,seconds)
        p.write_json(out/'supervisor.json',driver)
        self.assertEqual(driver['status'],'BUDGET_EXHAUSTED');self.assertTrue(marker.exists())
        self.assertTrue(driver['observed_checkpoints']);notice=max(driver['observed_checkpoints'],key=lambda c:c['gain'])
        self.assertGreater(notice['gain'],0)
        pid=json.loads(marker.read_text())['pid']
        with self.assertRaises(ProcessLookupError):os.kill(pid,0)
        notice_path=out/'selected_notice.json';p.write_json(notice_path,notice)
        # Separate process uses the unchanged full-content outer verifier.
        code=f'''import sys,json
from pathlib import Path
sys.path.insert(0,{str(p.PACKAGE/'nonlinear_divisors')!r})
import anytime as at
notice=json.loads(Path({str(notice_path)!r}).read_text())
path,metadata=at.verify_checkpoint(Path({str(out)!r}),notice,{p.sha(self.input)!r},free_domain_required=True)
print(json.dumps(dict(status='PASS',checkpoint=str(path),gain=notice['gain'])))
'''
        external=subprocess.run([sys.executable,'-B','-c',code],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
        (out/'external-verification.log').write_text(external.stdout);self.assertEqual(external.returncode,0,external.stdout)
        p.write_json(self.out/'result.json',dict(status='PASS',hard_timeout=True,prior_checkpoint_independently_verified=True,
            worker_process_gone=True,new_DSEC_runs=0,tiny_functional_fixture=True,performance_comparison='NOT_RUN'))

if __name__=='__main__':unittest.main()
