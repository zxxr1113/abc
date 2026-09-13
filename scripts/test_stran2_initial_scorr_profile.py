#!/usr/bin/env python3

import unittest

from stran_profile import NA, parse_experiment_profile


class InitialScorrProfileTest(unittest.TestCase):
    def test_absent_profile_is_na(self) -> None:
        profile = parse_experiment_profile("")
        self.assertEqual(profile["stran2_initial_scorr_records"], NA)
        self.assertEqual(profile["stran2_initial_scorr_bmc_unknown"], NA)

    def test_profile_fields_are_parsed(self) -> None:
        profile = parse_experiment_profile(
            "stran2 initial scorr profile: schema=1 frames=4 "
            "conflict-limit=10000 source-and=100 result-and=80 "
            "source-reg=10 result-reg=8 completed=1 rounds=3 "
            "bmc-unsat=11 bmc-sat=12 bmc-unknown=13 "
            "induction-unsat=21 induction-sat=22 induction-unknown=23 "
            "conflicts=456 total-sec=1.25 bmc-sec=0.25 "
            "induction-sec=0.75 reduce-sec=0.1."
        )
        self.assertEqual(profile["stran2_initial_scorr_records"], 1)
        self.assertEqual(profile["stran2_initial_scorr_frames"], 4)
        self.assertEqual(profile["stran2_initial_scorr_conflict_limit"], 10000)
        self.assertEqual(profile["stran2_initial_scorr_bmc_unknown"], 13)
        self.assertEqual(profile["stran2_initial_scorr_induction_unknown"], 23)
        self.assertEqual(profile["stran2_initial_scorr_total_sec"], 1.25)


if __name__ == "__main__":
    unittest.main()
