import os
import subprocess
import unittest

from stran_profile import NA, PROFILE_FIELDS, parse_experiment_profile


class SignatureGuideProfileTests(unittest.TestCase):
    def test_absent_profile_is_not_reported_as_zero_cost(self):
        r = parse_experiment_profile("")
        self.assertEqual(r["signature_guide_records"], NA)
        self.assertEqual(r["signature_guide_guide_sec"], NA)
        self.assertEqual(len(PROFILE_FIELDS), len(set(PROFILE_FIELDS)))

    def test_counts_sum_capacity_takes_max_and_sat_time_stays_nested(self):
        text = "\n".join([
            "stran-root signature-guide: schema=1 round=1 mode=2 roots=5 "
            "low=3 aliases=0 changed=3 split=2 conflicts=1 rows-before=200 "
            "rows-after=12 slots-max=6 sat=2 sat-yes=1 sat-no=0 sat-unknown=1 "
            "prep-sec=0.1 guide-sec=0.4 sat-sec=0.2",
            "stran-root signature-guide: schema=1 round=2 mode=2 roots=7 "
            "low=4 aliases=0 changed=4 split=4 conflicts=0 rows-before=300 "
            "rows-after=25 slots-max=4 sat=1 sat-yes=1 sat-no=0 sat-unknown=0 "
            "prep-sec=0.1 guide-sec=0.3 sat-sec=0.1",
        ])
        r = parse_experiment_profile(text)
        self.assertEqual(r["signature_guide_records"], 2)
        self.assertEqual(r["signature_guide_roots"], 12)
        self.assertEqual(r["signature_guide_rows_after"], 37)
        self.assertEqual(r["signature_guide_slots_max"], 6)
        self.assertEqual(r["signature_guide_sat_unknown"], 1)
        self.assertAlmostEqual(r["signature_guide_guide_sec"], 0.7)
        self.assertAlmostEqual(r["signature_guide_sat_sec"], 0.3)


@unittest.skipUnless(os.environ.get("ABC"), "set ABC to test the built command")
class SignatureGuideCommandTests(unittest.TestCase):
    def run_abc(self, command):
        env = dict(os.environ)
        env.pop("ABC_CEX_MODE", None)
        env.pop("ABC_CEX_COMPRESS", None)
        return subprocess.run([env["ABC"], "-c", command], env=env,
                              capture_output=True, text=True, timeout=30)

    def test_bad_modes_are_rejected_before_network_access(self):
        for mode in ("-1", "4", "abc", "2x", "999999999999999999999"):
            with self.subTest(mode=mode):
                p = self.run_abc(f"&stran2 -H {mode}")
                self.assertIn("usage: &stran2", p.stdout + p.stderr)

    def test_unsupported_configuration_is_explicit(self):
        p = self.run_abc("&stran2 -H 2")
        self.assertIn("-H requires", p.stdout + p.stderr)

    def test_control_does_not_require_the_new_preset(self):
        p = self.run_abc("&stran2 -H 0")
        self.assertIn("There is no AIG", p.stdout + p.stderr)
        self.assertNotIn("-H requires", p.stdout + p.stderr)


if __name__ == "__main__":
    unittest.main()
