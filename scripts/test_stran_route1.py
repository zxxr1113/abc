"""Route-one preset, stage isolation, and command-local policy regression."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
ABC = Path(os.environ.get('ABC_BIN', ROOT / 'abc')).resolve()


@unittest.skipUnless(ABC.is_file(), 'ABC executable is unavailable')
class Route1Test(unittest.TestCase):
    def run_abc(self, commands, **settings):
        env = {k: v for k, v in os.environ.items() if not k.startswith('ABC_')}
        env.update(settings)
        result = subprocess.run([str(ABC), '-q', commands], cwd=ROOT,
                                env=env, capture_output=True, text=True, timeout=120)
        return result, result.stdout + result.stderr

    def test_full_then_legacy_does_not_leak_policy(self):
        with tempfile.TemporaryDirectory() as tmp:
            before = Path(tmp) / 'before.aig'
            after = Path(tmp) / 'after.aig'
            result, text = self.run_abc(
                'read_blif test/stran_microbatch_helper.blif; strash; '
                f'write_aiger {before}; &get; &stran2 -A profile=route1 -p; '
                f'&write {after}; dsec {before} {after}; '
                f'&read {before}; &stran2 -A profile=strict-speed -p')
            self.assertEqual(result.returncode, 0, text)
            self.assertNotIn('Assertion', text)
            self.assertIn('Networks are equivalent', text)
            self.assertEqual(text.count('stran-root ODC pair-truth policy:'), 1)
            self.assertIn('enabled=1 scope=odc fixed-material-pool=1', text)
            self.assertIn('enabled=1 scope=odc-relational', text)
            self.assertIn('stran-window options: S=-1 cache=1 factor=1', text)
            self.assertIn('depth=4 max-extra-ands=80 F=1 C=1000', text)

    def test_strict_profile_has_no_odc_and_honors_later_override(self):
        result, text = self.run_abc(
            'read_blif test/stran_microbatch_helper.blif; strash; &get; '
            '&stran2 -A profile=route1-strict -A strict-w=1 -p')
        self.assertEqual(result.returncode, 0, text)
        self.assertIn('stran-strict options: S=0 w=1', text)
        self.assertNotIn('stran-root ODC pair-truth policy:', text)
        self.assertNotIn('stran-root relational-proof:', text)

    def test_invalid_proof_option_rejected_before_mutation(self):
        result, text = self.run_abc(
            'read_blif test/stran_microbatch_helper.blif; strash; &get; '
            '&stran2 -A profile=route1', ABC_ODC_RELATIONAL_PROOF='3')
        self.assertIn('ABC_ODC_RELATIONAL_PROOF must be an integer in [0,2]', text)
        self.assertNotIn('stran-strict options:', text)


if __name__ == '__main__':
    unittest.main()
