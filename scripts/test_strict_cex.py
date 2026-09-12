import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from stran_profile import NA, PROFILE_FIELDS, parse_experiment_profile


class StrictCexProfileTests(unittest.TestCase):
    def test_absent_is_not_zero(self):
        p = parse_experiment_profile("")
        self.assertEqual(p['strict_cex_active_seconds'], NA)
        self.assertEqual(len(PROFILE_FIELDS), len(set(PROFILE_FIELDS)))

    def test_cumulative_counters_take_last_epoch(self):
        p = parse_experiment_profile(
            'strict-cex epoch=1 mode=4 solver=1 bank=3 active-queries=64 active-seconds=0.1\n'
            'strict-cex epoch=2 mode=4 solver=1 bank=7 active-queries=128 active-seconds=0.25\n')
        self.assertEqual(p['strict_cex_records'], 2)
        self.assertEqual(p['strict_cex_bank'], 7)
        self.assertEqual(p['strict_cex_active_queries'], 128)
        self.assertEqual(p['strict_cex_active_seconds'], 0.25)


class StrictCexPresetTests(unittest.TestCase):
    def run_preset(self, **options):
        env = dict(os.environ, ABC='/bin/true', AIG_DIR='/dev/shm', DRY_RUN='1')
        env.update(ABC_STRICT_CEX_MODE='6', ABC_CEX_MODE='2', ABC_CEX_COMPRESS='4')
        env.update(options)
        with tempfile.TemporaryDirectory(dir='/dev/shm') as d:
            return subprocess.run(['bash', str(Path(__file__).with_name('run_stran2_strict_cex.sh'))],
                                  cwd=d, env=env, capture_output=True, text=True, timeout=30)

    def test_three_groups_override_inherited_teacher_settings(self):
        for odc, cex, text in [('0','0','initial=0 strict-mode=0'),
                               ('0','1','initial=1 strict-mode=4'),
                               ('1','1','initial=1 strict-mode=4')]:
            with self.subTest(odc=odc, cex=cex):
                p = self.run_preset(ODC_ENABLED=odc, CEX_ENABLED=cex)
                self.assertEqual(p.returncode, 0, p.stderr)
                self.assertIn(text, p.stdout)
                self.assertEqual('ODC-observation-mode=2' in p.stdout, odc == cex == '1')

    def test_bad_modes_rejected(self):
        for key, value in [('CEX_ENABLED','2'), ('ODC_ENABLED','x'),
                           ('STRICT_CEX_MODE','7'), ('STRICT_CEX_SOLVER','-1')]:
            with self.subTest(key=key):
                self.assertNotEqual(self.run_preset(**{key:value}).returncode, 0)


if __name__ == '__main__':
    unittest.main()
