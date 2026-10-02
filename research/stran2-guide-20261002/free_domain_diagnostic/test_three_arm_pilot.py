import copy
from collections import Counter
import contextlib
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import prepare_three_arm_pilot as prep
import run_three_arm_pilot as run

class Tests(unittest.TestCase):
    def fixtures(self):
        cases=[dict(file=f'{i}.aig',loaded_AND=100)for i in range(6)];ledger=[]
        for case in cases:
            for arm,gain in zip(run.ARMS,[2,1,3]):
                ledger.append(dict(case=case['file'],arm=arm,status='VALIDATED',
                    global_result=dict(global_hash_corrected_conditional_build_marginal=gain),analysis=dict(status='BUDGET_EXHAUSTED',
                    root_pools={'10':[[1,2],{}]},guidance={},candidate_ids=[],qualified_ids=[],selected_ids=[])))
        return dict(cases=cases),ledger
    def test_order_positions_and_pair_orders_balanced(self):
        rows=prep.orders();self.assertEqual(len(rows),6)
        for arm in run.ARMS:self.assertEqual(Counter(order.index(arm)for _,order in rows),{0:2,1:2,2:2})
        for a,b in [('inline_free_off','predecessor_cache_off'),('inline_free_off','predecessor_cache_on'),('predecessor_cache_off','predecessor_cache_on')]:
            self.assertEqual(sum(order.index(a)<order.index(b)for _,order in rows),3)
    def test_all_three_contrasts_and_timeout_missing_guidance(self):
        plan,ledger=self.fixtures();s=run.analyze(plan,ledger);self.assertEqual(s['status'],'COMPLETE')
        self.assertEqual({k:v['paired_and_difference']for k,v in s['contrasts'].items()},
                         dict(free_without_cache_minus_inline=-6,cache_effect_minus_uncached_free=12,cached_free_minus_inline=6))
        self.assertEqual(s['cases'][0]['contrasts']['cached_free_minus_inline']['initial_signature_identity'],'UNAVAILABLE_BEFORE_GUIDANCE_REPORT')
    def test_one_failed_arm_only_removes_its_two_pairs(self):
        plan,ledger=self.fixtures();ledger[1]['status']='FAILED';s=run.analyze(plan,ledger)
        self.assertEqual(s['contrasts']['cached_free_minus_inline']['valid_pairs'],6)
        self.assertEqual(s['contrasts']['cache_effect_minus_uncached_free']['valid_pairs'],5)
        self.assertEqual(s['contrasts']['free_without_cache_minus_inline']['valid_pairs'],5)
    def test_null_margin_stays_missing(self):
        plan,ledger=self.fixtures();ledger[2]['global_result']['global_hash_corrected_conditional_build_marginal']=None
        s=run.analyze(plan,ledger);self.assertIsNone(s['cases'][0]['arms']['predecessor_cache_on']['genuine_build_and'])
        self.assertEqual(s['contrasts']['cached_free_minus_inline']['valid_pairs'],5)
    def test_changed_common_pool_rejected(self):
        plan,ledger=self.fixtures();ledger[1]['analysis']['root_pools']['10']=[[1,3],{}]
        with self.assertRaisesRegex(ValueError,'pools differ'):run.analyze(plan,ledger)
    def test_changed_initial_signature_rejected(self):
        plan,ledger=self.fixtures();ledger[0]['analysis']['guidance']['pool_signature_sha256']='a';ledger[1]['analysis']['guidance']['pool_signature_sha256']='b'
        with self.assertRaisesRegex(ValueError,'signatures differ'):run.analyze(plan,ledger)
    def policy(self):
        return dict(minimum_start_free_gib=16,reserve_gib=4,minimum_job_growth_allowance_gib=2,observed_growth_multiplier=2)
    def usage(self,values):
        sequence=iter(values)
        return lambda _:SimpleNamespace(free=next(sequence)*1024**3)
    def test_start_capacity_requires_reserve_plus_planning_allowance(self):
        guard=run.DiskGuard('.',self.policy(),self.usage([15]))
        with self.assertRaises(run.DiskCapacityStop):guard.start()
    def test_larger_observed_job_growth_increases_next_allowance(self):
        guard=run.DiskGuard('.',self.policy(),self.usage([20,20,17,10,9]))
        guard.begin_job();guard.check('first');row=guard.finish_job()
        self.assertEqual(row['observed_free_space_consumption_bytes'],3*1024**3)
        guard.begin_job()
        with self.assertRaises(run.DiskCapacityStop):guard.check('second')
        self.assertEqual(guard.observations[-1]['required_bytes'],10*1024**3)
    def test_capacity_stop_preserves_all_missing_jobs_without_launch(self):
        plan,_=self.fixtures()
        with tempfile.TemporaryDirectory()as directory:
            root=Path(directory)
            plan.update(status='PREPARED_NOT_EXECUTED',workers=1,inline_cone_check=False,arms=list(run.ARMS),
                        disk_policy=self.policy(),source_freeze_sha256={},external_bindings={},
                        ordered_jobs=[dict(case=c['file'],arm=a,directory=str(root/c['file']/a))for c in plan['cases']for a in run.ARMS])
            path=root/'plan.json';run.write(path,plan)
            with patch.object(run.shutil,'disk_usage',side_effect=self.usage([20,6,5,5])), \
                 patch.object(run,'execute',side_effect=AssertionError('must not launch')),contextlib.redirect_stdout(io.StringIO()):
                run.run(path,run.sha(path),True)
            records=json.loads((root/'ledger.json').read_text())
            self.assertEqual(records[0]['status'],'DISK_CAPACITY_STOP')
            self.assertTrue(all(row['status']=='SKIPPED_DISK_CAPACITY'for row in records[1:]))
            self.assertEqual(len(records),18)
            self.assertTrue(all(row['valid_pairs']==0 for row in json.loads((root/'summary.json').read_text())['contrasts'].values()))

if __name__=='__main__':unittest.main()
