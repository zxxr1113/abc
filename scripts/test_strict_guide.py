import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from stran_profile import NA, PROFILE_FIELDS, parse_experiment_profile


class StrictGuideTests(unittest.TestCase):
    def test_absent_is_not_zero(self):
        p = parse_experiment_profile("")
        self.assertEqual(p['strict_guide_auxiliary_rows'], NA)
        self.assertEqual(len(PROFILE_FIELDS), len(set(PROFILE_FIELDS)))

    def test_snapshot_sum_and_overflow(self):
        p = parse_experiment_profile(
            'stran-root strict-signature-guide: schema=1 snapshots=1 source-rows=2048 auxiliary-rows=256 skipped-overflow=0 prep-sec=0.1\n'
            'stran-root strict-signature-guide: schema=1 snapshots=1 source-rows=2048 auxiliary-rows=256 skipped-overflow=0 prep-sec=0.2\n'
            'stran-root strict-signature-guide: schema=1 snapshots=0 source-rows=0 auxiliary-rows=0 skipped-overflow=1 prep-sec=0\n'
            'strict-cex epoch=1 bank=3 active-queries=64\n'
            'strict-cex epoch=2 bank=7 active-queries=128\n')
        self.assertEqual(p['strict_guide_records'], 3)
        self.assertEqual(p['strict_guide_snapshots'], 2)
        self.assertEqual(p['strict_guide_auxiliary_rows'], 512)
        self.assertEqual(p['strict_guide_skipped_overflow'], 1)
        self.assertAlmostEqual(p['strict_guide_prep_sec'], 0.3)
        self.assertEqual(p['strict_cex_active_queries'], 128)

    def run_preset(self, **options):
        env = dict(os.environ, ABC='/bin/true', AIG_DIR='/dev/shm', DRY_RUN='1',
                   STRICT_GUIDE='1', STRICT_BOTH_POLARITIES='1',
                   ABC_STRICT_GUIDE='0', ABC_STRICT_BOTH_POLARITIES='0')
        env.update(options)
        with tempfile.TemporaryDirectory(dir='/dev/shm') as d:
            return subprocess.run(['bash', str(Path(__file__).with_name('run_stran2_strict_guide.sh'))],
                                  cwd=d, env=env, capture_output=True, text=True, timeout=30)

    def test_default_and_disabled(self):
        for value in ['0', '1']:
            p = self.run_preset(STRICT_GUIDE=value, STRICT_BOTH_POLARITIES=value)
            self.assertEqual(p.returncode, 0, p.stderr)
            self.assertIn('both-polarities=' + value + ' auxiliary-free-state-signature=' + value, p.stdout)

    def test_invalid_mode(self):
        for key in ['STRICT_GUIDE', 'STRICT_BOTH_POLARITIES']:
            self.assertNotEqual(self.run_preset(**{key: '2'}).returncode, 0)


if __name__ == '__main__':
    unittest.main()
