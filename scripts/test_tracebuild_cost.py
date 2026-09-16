import unittest

from stran_profile import parse_experiment_profile


class TraceBuildCostProfileTest(unittest.TestCase):
    def test_cost_and_structural_cut_records_accumulate(self):
        profile = parse_experiment_profile("\n".join([
            "tracebuild-cost root=7 enabled=1 evaluated=9 rejected=2 old-bound-excluded=3 old-bound-positive=1 old-bound-proved=1 zero-new-proved=0 zero-new-commits=0 raw-gates=20 new-gates=11",
            "tracebuild-cut root=7 enabled=1 multi=1 views=5 capped=0 kit=5 bdc=4 positive=2 proofs=1 commit-kit=1 commit-bdc=0 old-bound-excluded=2 old-bound-positive=1 old-bound-proved=1 raw-gates=13 new-gates=7",
            "tracebuild-cut root=9 enabled=1 multi=1 views=3 capped=1 kit=3 bdc=2 positive=1 proofs=0 commit-kit=0 commit-bdc=0 old-bound-excluded=1 old-bound-positive=1 old-bound-proved=0 raw-gates=8 new-gates=5",
        ]))
        self.assertEqual(profile["tracebuild_cost_evaluated"], 9)
        self.assertEqual(profile["tracebuild_old_bound_positive"], 1)
        self.assertEqual(profile["tracebuild_cut_views"], 8)
        self.assertEqual(profile["tracebuild_cut_capped"], 1)
        self.assertEqual(profile["tracebuild_cut_kit"], 8)
        self.assertEqual(profile["tracebuild_cut_bdc"], 6)
        self.assertEqual(profile["tracebuild_cut_positive"], 3)
        self.assertEqual(profile["tracebuild_cut_multi"], 2)
        self.assertEqual(profile["tracebuild_cut_commit_kit"], 1)
        self.assertEqual(profile["tracebuild_cut_old_bound_excluded"], 3)
        self.assertEqual(profile["tracebuild_cut_old_bound_positive"], 2)
        self.assertEqual(profile["tracebuild_cut_old_bound_proved"], 1)
        self.assertEqual(profile["tracebuild_cut_raw_gates"], 21)
        self.assertEqual(profile["tracebuild_cut_new_gates"], 12)


if __name__ == "__main__":
    unittest.main()
