#!/usr/bin/env python3
"""Cheap orchestration tests only; never invoke a solver or benchmark case."""
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('full_cohort_run', HERE / 'run.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)


class RunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(dir='/workspace/shared')
        self.root = Path(self.temp.name)
        self.cases = [dict(file=f'{i:03d}_case.aig', loaded_AND=100) for i in range(55)]
        self.protocol = dict(cases=self.cases, waves=r.waves(self.cases), config=r.CONFIG,
                             scope='test', attribution_cost='extra')

    def tearDown(self):
        self.temp.cleanup()

    def test_all55_exact_once_per_arm(self):
        waves = r.waves(self.cases)
        self.assertEqual(len(waves), 56)
        for arm in r.ARMS:
            self.assertEqual([c for w in waves if w['arm'] == arm for c in w['cases']], [c['file'] for c in self.cases])

    def test_wave_barrier_and_balanced_arm_order(self):
        waves = r.waves(self.cases)
        for a, b in zip(waves[::2], waves[1::2]):
            self.assertEqual(a['cases'], b['cases'])
            self.assertEqual({a['arm'], b['arm']}, set(r.ARMS))
            self.assertLessEqual(len(a['cases']), 2)
        self.assertEqual([w['arm'] for w in waves[::2]].count('ordinary'), 14)
        self.assertEqual([w['arm'] for w in waves[::2]].count('imageguided'), 14)

    def test_cli_only_optin_differs(self):
        tools = {name: self.root / name for name in ('solver', 'abc', 'image_model_solver')}
        ordinary, image = r.waves(self.cases)[:2]
        a = r.transform_command(self.protocol, self.root, tools, ordinary, self.root)
        b = r.transform_command(self.protocol, self.root, tools, image, self.root)
        self.assertNotIn('--image-model-solver', a)
        self.assertEqual(b[-2:], ['--image-model-solver', str(tools['image_model_solver'])])
        for cmd in (a, b):
            self.assertEqual(cmd[cmd.index('--workers') + 1], '2')
            self.assertEqual(cmd[cmd.index('--wall-seconds') + 1], '120.0')
            self.assertEqual(cmd[cmd.index('--dsec-seconds') + 1], '120')
            self.assertEqual(cmd[cmd.index('--pool-cap') + 1], '24')

    def test_missing_error_and_not_started_retained(self):
        rows = r.ledger(self.protocol)
        wave = self.protocol['waves'][0]
        r.merge_wave(rows, wave, [dict(file=wave['cases'][0], status='BUDGET_EXHAUSTED', search_complete=False, product=None)])
        self.assertEqual(len(rows), 110)
        self.assertEqual(sum(x['status'] == 'ERROR' for x in rows), 1)
        self.assertEqual(sum(x['status'] == 'BUDGET_EXHAUSTED' for x in rows), 1)
        self.assertEqual(sum(x['status'] == 'NOT_STARTED' for x in rows), 108)
        self.assertIsNone(next(x for x in rows if x['status'] == 'ERROR')['product'])

    def test_unknown_result_rejected(self):
        with self.assertRaises(ValueError):
            r.merge_wave(r.ledger(self.protocol), self.protocol['waves'][0], [dict(file='other.aig')])

    def test_duplicate_result_rejected(self):
        row = dict(file=self.cases[0]['file'])
        with self.assertRaises(ValueError):
            r.merge_wave(r.ledger(self.protocol), self.protocol['waves'][0], [row, row])

    def test_capacity_is_evidence_based(self):
        policy = r.capacity_policy({'solver': dict(bytes=100)})
        self.assertGreater(policy['worst_observed_scenario_bytes'], 50 * r.GIB)
        self.assertFalse(policy['estimate_is_hard_upper_bound'])
        self.assertGreater(policy['wave_free_disk_bytes'], 4 * r.GIB)
        self.assertLess(policy['initial_free_disk_bytes'], 7 * r.GIB)

    def test_resource_floor_blocks_current_low_disk(self):
        policy = r.capacity_policy({})
        with patch.object(r.shutil, 'disk_usage', return_value=SimpleNamespace(free=5 * r.GIB)):
            with self.assertRaisesRegex(ValueError, 'insufficient free disk'):
                r.resources(self.root, policy, initial=True)

    def test_corrected_summary_uses_paired_gains_and_integrity(self):
        r.write(self.root / 'protocol.json', self.protocol)
        rows = r.ledger(self.protocol)
        for row in rows:
            row['status'] = 'BUDGET_EXHAUSTED'
        r.write(self.root / 'results.json', rows)
        for wave, gain in [(0, 2), (1, 7)]:
            directory = self.root / 'audits' / f'wave_{wave:03d}_global'
            directory.mkdir(parents=True)
            r.write(directory / 'results.json', [dict(case='000_case', status='GLOBAL_STRUCTURAL_ALIAS_ACCOUNTING_COMPLETE',
                          global_hash_corrected_conditional_build_marginal=gain)])
            r.write(directory / 'integrity.json', dict(status='PASS'))
        r.summarize(SimpleNamespace(out=self.root))
        summary = r.read(self.root / 'corrected_summary.json')
        self.assertEqual(summary['paired']['cases'], 1)
        self.assertEqual(summary['paired']['delta_and'], 5)
        self.assertEqual(summary['paired']['equal_case_delta_pp'], 5)
        self.assertEqual(len(summary['excluded_cases']), 54)
        (self.root / 'audits/wave_001_global/integrity.json').unlink()
        r.summarize(SimpleNamespace(out=self.root))
        self.assertEqual(r.read(self.root / 'corrected_summary.json')['paired']['cases'], 0)
        self.assertEqual(len(r.read(self.root / 'corrected_rows.json')), 110)

    def test_initial_admission_failure_retains_all110(self):
        protocol = dict(self.protocol, runner_sha256=r.sha(r.__file__), resource_policy=r.capacity_policy({}))
        source = self.root / 'protocol.json'
        r.write(source, protocol)
        out = self.root / 'output'
        with patch.object(r, 'resources', side_effect=ValueError('insufficient free disk')), \
             patch.object(r, 'copy_frozen') as copy:
            r.transform(SimpleNamespace(protocol=source, out=out))
        copy.assert_not_called()
        self.assertEqual(r.read(out / 'coverage.json')['statuses'], {'NOT_STARTED': 110})
        self.assertEqual(len(r.read(out / 'results.json')), 110)

    def test_capacity_stop_preserves_entire_plan_without_launching_later_wave(self):
        protocol = dict(self.protocol, runner_sha256=r.sha(r.__file__), tools={},
                        resource_policy=r.capacity_policy({}))
        source = self.root / 'protocol.json'
        r.write(source, protocol)
        out = self.root / 'output'
        tools = {name: self.root / name for name in ('solver', 'abc', 'image_model_solver')}
        calls = []
        def fake_execute(command, log):
            calls.append(command)
            run = Path(command[command.index('--out') + 1])
            run.mkdir(parents=True)
            names = command[command.index('--cases') + 1:command.index('--solver')]
            r.write(run / 'results.json', [dict(file=name, status='COMPLETE', search_complete=True, product=None) for name in names])
            return dict(command=command, exit_code=0, outer_wall_s=0)
        with patch.object(r, 'resources', side_effect=[{}, {}, {}, ValueError('insufficient free disk')]), \
             patch.object(r, 'copy_frozen', return_value=(self.root, tools)), \
             patch.object(r, 'verify'), patch.object(r, 'execute', side_effect=fake_execute):
            r.transform(SimpleNamespace(protocol=source, out=out))
        self.assertEqual(len(calls), 2)
        self.assertEqual(r.read(out / 'capacity_stop.json')['remaining_not_started'], 106)
        self.assertEqual(len(r.read(out / 'results.json')), 110)
        self.assertEqual(r.read(out / 'coverage.json')['statuses'], {'COMPLETE': 4, 'NOT_STARTED': 106})

    def paused_between_arms(self, status='COMPLETE'):
        protocol = dict(self.protocol, runner_sha256=r.sha(r.__file__),
                        tools={name: {} for name in ('solver', 'abc', 'image_model_solver')},
                        resource_policy=r.capacity_policy({}))
        source = self.root / 'protocol.json'
        r.write(source, protocol)
        out = self.root / 'paused'
        tools = {name: out / 'tools' / name for name in protocol['tools']}
        def fake_copy(*unused):
            (out / 'frozen_package').mkdir()
            (out / 'tools').mkdir()
            for path in tools.values():
                path.write_text('frozen test tool')
            return out / 'frozen_package', tools
        def fake_execute(command, log):
            log.write_text('synthetic driver log; no subprocess executed')
            run = Path(command[command.index('--out') + 1])
            run.mkdir(parents=True)
            names = command[command.index('--cases') + 1:command.index('--solver')]
            r.write(run / 'results.json', [dict(file=name, status=status, search_complete=status == 'COMPLETE', product=None) for name in names])
            r.write(run / 'plan.json', {'cases': names})
            r.write(run / 'source_integrity.json', {'status': 'PASS'})
            return dict(command=command, exit_code=0, outer_wall_s=0)
        with patch.object(r, 'resources', side_effect=[{}, {}, ValueError('insufficient free disk')]), \
             patch.object(r, 'copy_frozen', side_effect=fake_copy), patch.object(r, 'verify'), \
             patch.object(r, 'execute', side_effect=fake_execute):
            r.transform(SimpleNamespace(protocol=source, out=out))
        return out, fake_execute

    def test_resume_between_arms_preserves_completed_artifacts(self):
        out, execute = self.paused_between_arms()
        prior = {str(p.relative_to(out)): r.sha(p) for p in (out / 'runs/block_000/ordinary').rglob('*') if p.is_file()}
        with patch.object(r, 'resources', side_effect=[{}, ValueError('insufficient free disk')]), \
             patch.object(r, 'verify'), patch.object(r, 'execute', side_effect=execute) as run:
            r.resume(SimpleNamespace(out=out))
        self.assertEqual(run.call_count, 1)
        self.assertIn('--image-model-solver', run.call_args.args[0])
        self.assertTrue(all(r.sha(out / name) == digest for name, digest in prior.items()))
        self.assertEqual(len(r.read(out / 'attempt_history.json')), 2)
        self.assertEqual(len(list((out / 'capacity_stops').glob('*.json'))), 2)
        self.assertEqual(r.read(out / 'coverage.json')['statuses'], {'COMPLETE': 4, 'NOT_STARTED': 106})

    def test_resume_does_not_retry_error_wave(self):
        out, execute = self.paused_between_arms(status='ERROR')
        with patch.object(r, 'resources', side_effect=[{}, ValueError('insufficient free disk')]), \
             patch.object(r, 'verify'), patch.object(r, 'execute', side_effect=execute) as run:
            r.resume(SimpleNamespace(out=out))
        self.assertEqual(run.call_count, 1)
        self.assertIn('--image-model-solver', run.call_args.args[0])
        self.assertEqual(r.read(out / 'coverage.json')['statuses'], {'ERROR': 4, 'NOT_STARTED': 106})

    def test_resume_protocol_drift_denied_before_execution(self):
        out, _ = self.paused_between_arms()
        protocol = r.read(out / 'protocol.json')
        protocol['scope'] = 'changed'
        r.write(out / 'protocol.json', protocol)
        before = r.sha(out / 'attempt_history.json')
        with patch.object(r, 'execute') as execute:
            with self.assertRaisesRegex(ValueError, 'protocol drift'):
                r.resume(SimpleNamespace(out=out))
        execute.assert_not_called()
        self.assertEqual(r.sha(out / 'attempt_history.json'), before)

    def test_resume_frozen_tool_drift_denied_before_execution(self):
        out, _ = self.paused_between_arms()
        before = r.sha(out / 'attempt_history.json')
        with patch.object(r, 'verify', side_effect=ValueError('tool drift: solver')), patch.object(r, 'execute') as execute:
            with self.assertRaisesRegex(ValueError, 'tool drift'):
                r.resume(SimpleNamespace(out=out))
        execute.assert_not_called()
        self.assertEqual(r.sha(out / 'attempt_history.json'), before)

    def test_resume_ambiguous_unstarted_artifacts_denied(self):
        out, _ = self.paused_between_arms()
        (out / 'runs/block_000/imageguided').mkdir()
        with patch.object(r, 'execute') as execute:
            with self.assertRaisesRegex(ValueError, 'ambiguous existing artifacts'):
                r.resume(SimpleNamespace(out=out))
        execute.assert_not_called()

    def test_resume_completed_metadata_drift_denied(self):
        out, _ = self.paused_between_arms()
        (out / 'runs/block_000/ordinary/results.json').write_text('[]')
        with patch.object(r, 'execute') as execute:
            with self.assertRaisesRegex(ValueError, 'metadata drift'):
                r.resume(SimpleNamespace(out=out))
        execute.assert_not_called()

    def test_mixed_wave_state_denied(self):
        rows = r.ledger(self.protocol)
        rows[0]['status'] = 'ERROR'
        with self.assertRaisesRegex(ValueError, 'partially started wave'):
            r.pending_wave(rows, self.protocol['waves'][0])

    def test_summary_retains_direct_unknown_and_dsec_status(self):
        r.write(self.root / 'protocol.json', self.protocol)
        rows = r.ledger(self.protocol)
        for row in rows:
            row.update(status='BUDGET_EXHAUSTED', product={'baseline_dsec': {'status': 'PASS'}, 'independent_dsec': {'status': 'UNKNOWN'}})
        r.write(self.root / 'results.json', rows)
        direct = self.root / 'audits/wave_000_direct'
        direct.mkdir(parents=True)
        r.write(direct / 'results.json', [dict(case='000_case', status='ATTRIBUTION_AUDIT_COMPLETE',
                                               direct_proof={'unknown_not_cached': 3}, arms={'mixed': {'dsec': {'status': 'TIMEOUT'}}})])
        r.summarize(SimpleNamespace(out=self.root))
        row = r.read(self.root / 'corrected_rows.json')[0]
        self.assertEqual(row['direct_unknown_queries'], 3)
        self.assertEqual(row['transform_dsec']['independent_dsec'], 'UNKNOWN')
        self.assertEqual(row['direct_dsec']['mixed'], 'TIMEOUT')
        self.assertIsNone(row['corrected_gain'])
        summary = r.read(self.root / 'corrected_summary.json')
        self.assertEqual(summary['direct_unknown_queries_by_arm']['ordinary'], 3)
        self.assertEqual(summary['paired']['cases'], 0)

    def test_frozen_dependency_lists_include_both_auditors(self):
        self.assertIn('image_cegar_diagnostic/audit_online_products.py', r.EXTRA)
        self.assertIn('image_cegar_diagnostic/audit_global_alias_products.py', r.EXTRA)
        self.assertIn('nonlinear_divisors/hash_direct_audit.py', r.EXTRA)
        base = r.assignment(r.PACKAGE / 'nonlinear_divisors/anytime.py', 'RUNTIME')
        self.assertIn('nonlinear_divisors/product.py', base)


if __name__ == '__main__':
    unittest.main()
