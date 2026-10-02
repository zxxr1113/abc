"""Preparation/approval-gate tests; never execute a benchmark job."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import prepare_pilot as prep
import run_prepared_pilot as ctl

class PilotControllerTests(unittest.TestCase):
    def test_explicit_gate_precedes_any_plan_io_or_subprocess(self):
        with patch.object(ctl.subprocess,'Popen') as popen,patch.object(ctl,'read') as read:
            with self.assertRaisesRegex(ValueError,'Explicit GO'):ctl.run('/nonexistent/plan.json',False)
            popen.assert_not_called();read.assert_not_called()

    def test_fixed_order_alternates_without_replacing_cases(self):
        rows=prep.orders();self.assertEqual([x[0] for x in rows],prep.CASES)
        self.assertEqual([x[1][0] for x in rows],['baseline','predecessor_free']*3)
        self.assertEqual(len(rows)*2,12);self.assertEqual(prep.CONFIG['wall_seconds']*len(rows)*2,1440)

    def test_prepare_freezes_flags_tools_and_fresh_auditor_without_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);package=root/'package';package.mkdir();rows=[]
            for filename in ['nonlinear_divisors/anytime.py','nonlinear_divisors/image_guided.py',
                'nonlinear_divisors/inline_models.py','nonlinear_divisors/free_guided.py']:
                p=package/filename;p.parent.mkdir(exist_ok=True);p.write_text('RUNTIME = ['+repr(filename)+']\n')
            for filename in prep.AUDITORS:
                p=package/filename;p.parent.mkdir(exist_ok=True);p.write_text('# frozen auditor\n')
            for name in prep.CASES:
                row=dict(file=name,loaded_AND=100,first_seq_path='inputs/first_seq/'+name,loaded_path='inputs/loaded/'+name)
                for kind in ['first_seq','loaded']:
                    p=package/row[kind+'_path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'fixture '+name.encode());row[kind+'_sha256']=prep.sha(p)
                rows.append(row)
            (package/'cases.json').write_text(json.dumps(dict(cases=rows)))
            solver=root/'solver';solver.write_bytes(b'solver');abc=root/'abc';abc.write_bytes(b'abc');out=root/'prepared'
            with patch.object(prep,'PACKAGE',package),patch.object(prep.subprocess,'check_output',return_value='head\n'),\
                 patch.object(ctl.subprocess,'Popen') as process:
                plan=prep.prepare(out,solver,abc)
                process.assert_not_called()
            self.assertEqual(plan['status'],'PREPARED_NOT_EXECUTED');self.assertFalse((out/'execution.json').exists())
            self.assertFalse(plan['inline_cone_check']);self.assertEqual(plan['global_added_free_cap'],256)
            for job in plan['ordered_jobs']:
                command=job['command'];self.assertIn('--inline-image-models',command)
                self.assertEqual('--predecessor-free' in command,job['arm']=='predecessor_free')
                self.assertNotIn('--inline-cone-check',command);self.assertEqual(command[command.index('--workers')+1],'1')
                self.assertEqual(command[command.index('--wall-seconds')+1],'120.0')
                self.assertNotIn('--reuse-audit',command)
            for path,digest in plan['source_freeze_sha256'].items():self.assertEqual(prep.sha(out/path),digest)
            self.assertIn('without --reuse-audit',plan['fresh_audit_policy'])

    def test_watchdog_keeps_kill_stage_after_owned_group_leader_exits(self):
        class Process:
            pid=10
            def poll(self):return 0
            def wait(self,timeout):return 0
        old=dict(pid=10,start='old',pgid=10);alive=[True]
        def info(pid):return old if alive[0] else None
        def kill(pid,sig):alive[0]=False
        with patch.object(ctl,'descendants',return_value={}),patch.object(ctl,'proc_info',side_effect=info),\
             patch.object(ctl.os,'kill',side_effect=kill),patch.object(ctl.os,'killpg') as group,\
             patch.object(ctl.os,'getpgrp',return_value=999),patch.object(ctl.time,'sleep'):
            ctl.stop_owned(Process(),{10:old})
        self.assertEqual([c.args for c in group.call_args_list],[(10,ctl.signal.SIGTERM),(10,ctl.signal.SIGKILL)])

    def test_missing_arms_are_not_zero_area(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);plan=dict(cases=[dict(file=name,loaded_AND=100) for name in prep.CASES])
            ctl.analyze(root,plan,[]);report=ctl.read(root/'summary.json')
            self.assertEqual(report['valid_pairs'],0);self.assertIsNone(report['paired_and_difference'])
            self.assertEqual(report['status'],'INCOMPLETE_PAIRED_COVERAGE')

    def test_budget_incumbent_uses_last_completed_guidance_and_null_is_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);source=root/'run/005_b03';(source/'checkpoints/checkpoint_00000').mkdir(parents=True)
            ctl.write(source/'checkpoints/checkpoint_00000/checkpoint.json',dict(progress={}))
            result=dict(status='BUDGET_EXHAUSTED',search_complete=False,transform=dict(status='BUDGET_EXHAUSTED',error='timeout'),
                last_completed_chunk=dict(metrics=dict(positive_sampled_candidates=9),image_guidance=dict(pool_signature_sha256='same')),
                driver=dict(observed_checkpoints=[dict(directory='checkpoint_00000')],transform_process_wall_s=120,hard_transform_budget_s=120))
            ctl.write(source/'result.json',result)
            analysis=ctl.collect_case(root/'run','005_b03.aig')
            self.assertEqual(analysis['guidance']['pool_signature_sha256'],'same')
            self.assertEqual(analysis['positive_funnel']['positive_sampled_candidates'],9)
            self.assertEqual(analysis['guidance_evidence_source'],'last_completed_chunk')
            plan=dict(cases=[dict(file='005_b03.aig',loaded_AND=100)])
            ledger=[dict(case='005_b03.aig',arm=arm,status='VALIDATED',analysis=analysis,
                         global_result=dict(global_hash_corrected_conditional_build_marginal=value))
                    for arm,value in [('baseline',1),('predecessor_free',2)]]
            ctl.analyze(root,plan,ledger);summary=ctl.read(root/'summary.json')
            self.assertEqual(summary['cases'][0]['paired_and_difference'],1)
            ledger[1]['global_result']['global_hash_corrected_conditional_build_marginal']=None
            ctl.analyze(root,plan,ledger);summary=ctl.read(root/'summary.json')
            self.assertEqual(summary['cases'][0]['missing_or_failed_arms'],['predecessor_free'])
            self.assertIsNone(summary['paired_and_difference'])

    def test_timeout_before_guidance_reports_unavailable_without_crashing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);source=root/'run/005_b03';source.mkdir(parents=True)
            ctl.write(source/'result.json',dict(status='BUDGET_EXHAUSTED',driver=dict(observed_checkpoints=[],
                transform_process_wall_s=120,hard_transform_budget_s=120),transform=dict(status='BUDGET_EXHAUSTED')))
            analysis=ctl.collect_case(root/'run','005_b03.aig');self.assertEqual(analysis['guidance_evidence_source'],'UNAVAILABLE')
            plan=dict(cases=[dict(file='005_b03.aig',loaded_AND=100)])
            ledger=[dict(case='005_b03.aig',arm=arm,status='VALIDATED',analysis=analysis,
                         global_result=dict(global_hash_corrected_conditional_build_marginal=0)) for arm in ['baseline','predecessor_free']]
            ctl.analyze(root,plan,ledger);row=ctl.read(root/'summary.json')['cases'][0]
            self.assertEqual(row['initial_pool_signature_identity'],'UNAVAILABLE_BEFORE_GUIDANCE_REPORT')
            self.assertEqual(row['paired_and_difference'],0)

    def test_plan_mutation_rejects_against_approved_hash(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);path=root/'plan.json';ctl.write(path,dict(case='approved'))
            approved=ctl.sha(path);ctl.write(path,dict(case='changed'))
            with patch.object(ctl.subprocess,'Popen') as process:
                with self.assertRaisesRegex(ValueError,'approved plan changed'):ctl.run(path,True,approved)
                process.assert_not_called()
            self.assertFalse((root/'execution.json').exists())

    def test_frozen_source_drift_fails_before_execution_record_or_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);source=root/'source';source.write_bytes(b'changed')
            plan=dict(status='PREPARED_NOT_EXECUTED',approval_required=True,workers=1,inline_cone_check=False,
                python=__import__('sys').executable,python_sha256=ctl.sha(__import__('sys').executable),source_freeze_sha256={'source':'0'*64})
            ctl.write(root/'plan.json',plan)
            with patch.object(ctl.shutil,'disk_usage',return_value=type('Disk',(),{'free':8*1024**3})()),patch.object(ctl.subprocess,'Popen') as process:
                with self.assertRaisesRegex(ValueError,'prepared source/input/tool changed'):ctl.run(root/'plan.json',True,ctl.sha(root/'plan.json'))
                process.assert_not_called()
            self.assertFalse((root/'execution.json').exists())

if __name__=='__main__':unittest.main()
