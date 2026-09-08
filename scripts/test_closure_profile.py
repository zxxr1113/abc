import unittest

from stran_profile import parse_experiment_profile, validate_profile_accounting


def commit(phase, scope, before, after, selected, gains):
    rows = [
        f"stran-root experiment-time profile: schema=8 phase={phase} scope={scope} total-sec=1",
        f"stran-root experiment-summary profile: schema=8 phase={phase} scope={scope} selected-roots={sum(selected)} marginal-and={sum(gains)} final-and-gain={before-after} final-reg-gain=0 and-before={before} and-after={after} reg-before=1 reg-after=1",
    ]
    for kind, count, gain in zip(("constant", "existing", "build"), selected, gains):
        rows.append(f"stran-root experiment-commit profile: schema=8 phase={phase} kind={kind} selected={count} marginal-and={gain} marginal-reg=0")
    return rows


class ClosureProfileTest(unittest.TestCase):
    def setUp(self):
        self.rows = commit("comb", "discovery", 20, 19, (0, 0, 1), (0, 0, 1))
        self.rows += commit("seq", "discovery", 19, 17, (0, 0, 1), (0, 0, 2))
        self.rows += commit("seq", "closure", 17, 14, (0, 1, 1), (0, 1, 1))
        self.rows += commit("seq", "closure", 14, 14, (0, 0, 0), (0, 0, 0))
        self.rows += commit("seq", "discovery", 14, 14, (0, 0, 0), (0, 0, 0))

    def test_closure_and_cleanup_are_counted_once(self):
        result = parse_experiment_profile("\n".join(self.rows))
        self.assertEqual(result["comb_stage_and_gain"], 1)
        self.assertEqual(result["seq_stage_and_gain"], 5)
        self.assertEqual(result["seq_build_ordered_and_gain"], 3)
        self.assertEqual(result["seq_commit_build_selected"], 2)
        self.assertEqual(result["seq_commit_cleanup_extra_and_gain"], 1)
        self.assertEqual(result["profile_closure_records"], 2)
        self.assertEqual(result["profile_closure_selected"], 2)
        self.assertEqual(result["profile_closure_and_gain"], 3)
        self.assertEqual(result["profile_total_sec"], 5)
        validate_profile_accounting(result, 14)
        with self.assertRaises(ValueError):
            validate_profile_accounting(result, 13)

    def test_odc_bundle_is_ordered_build_once(self):
        rows = self.rows + commit("seq", "odc", 14, 8, (0, 0, 3), (0, 0, 6))
        rows += commit("seq", "odc", 8, 8, (0, 0, 0), (0, 0, 0))
        result = parse_experiment_profile("\n".join(rows))
        self.assertEqual(result["seq_build_ordered_and_gain"], 9)
        self.assertEqual(result["seq_commit_build_selected"], 5)
        self.assertEqual(result["seq_stage_and_gain"], 11)
        self.assertEqual(result["profile_total_sec"], 7)
        validate_profile_accounting(result, 8)

    def test_odc_direct_does_not_become_ordered_build(self):
        rows = self.rows + commit("seq", "odc", 14, 11, (1, 1, 0), (1, 2, 0))
        result = parse_experiment_profile("\n".join(rows))
        self.assertEqual(result["seq_build_ordered_and_gain"], 3)
        self.assertEqual(result["seq_commit_constant_and_gain"], 1)
        self.assertEqual(result["seq_commit_existing_and_gain"], 3)
        self.assertEqual(result["seq_stage_and_gain"], 8)
        validate_profile_accounting(result, 11)

    def test_odc_mixed_ordered_kind_attribution(self):
        rows = self.rows + commit("seq", "odc", 14, 8, (2, 1, 3), (2, 1, 3))
        result = parse_experiment_profile("\n".join(rows))
        self.assertEqual(result["seq_build_ordered_and_gain"], 6)
        self.assertEqual(result["seq_commit_constant_and_gain"], 2)
        self.assertEqual(result["seq_commit_existing_and_gain"], 2)
        self.assertEqual(result["seq_stage_and_gain"], 11)
        validate_profile_accounting(result, 8)

    def test_missing_commit_kind_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_experiment_profile("\n".join(self.rows[:-1]))

    def test_duplicate_commit_is_rejected(self):
        with self.assertRaises(ValueError):
            parse_experiment_profile("\n".join(self.rows + commit("seq", "closure", 17, 14, (0, 1, 1), (0, 1, 1))))

    def test_old_profile_is_not_claimed_complete(self):
        result = parse_experiment_profile("stran-root experiment-summary profile: schema=5 phase=seq selected-roots=1 marginal-and=1 final-and-gain=1 final-reg-gain=0 and-before=2 and-after=1 reg-before=1 reg-after=1")
        self.assertEqual(result["seq_stage_and_gain"], 1)
        self.assertEqual(result["profile_accounting_complete"], "N/A")

    def test_kit_portfolio_is_aggregated_by_phase(self):
        lines = [
            "stran-root Kit portfolio profile: schema=2 phase=comb core-max=8 calls=0 separated=0 synthesized=0 accepted=0 generated=0 submitted=0 proved=0 selected=0 selected-and-gain=0.",
            "stran-root Kit portfolio profile: schema=2 phase=seq core-max=8 calls=10 separated=8 synthesized=6 accepted=4 generated=4 submitted=3 proved=2 selected=1 selected-and-gain=5.",
            "stran-root Kit portfolio profile: schema=2 phase=seq core-max=10 calls=7 separated=6 synthesized=5 accepted=3 generated=3 submitted=3 proved=2 selected=2 selected-and-gain=9.",
        ]
        result = parse_experiment_profile("\n".join(lines))
        self.assertEqual(result["root_kit_core_max"], 10)
        self.assertEqual(result["root_kit_calls"], 17)
        self.assertEqual(result["root_seq_kit_accepted"], 7)
        self.assertEqual(result["root_seq_kit_proved"], 4)
        self.assertEqual(result["root_seq_kit_selected"], 3)
        self.assertEqual(result["root_seq_kit_selected_and_gain"], 14)
        self.assertEqual(result["root_comb_kit_calls"], 0)

    def test_bdc_portfolio_is_aggregated_by_phase(self):
        lines = [
            "stran-root BDC portfolio profile: schema=1 phase=comb core-max=8 calls=0 separated=0 synthesized=0 accepted=0 generated=0 submitted=0 proved=0 selected=0 selected-and-gain=0.",
            "stran-root BDC portfolio profile: schema=1 phase=seq core-max=8 calls=9 separated=7 synthesized=4 accepted=3 generated=3 submitted=3 proved=2 selected=1 selected-and-gain=6.",
        ]
        result = parse_experiment_profile("\n".join(lines))
        self.assertEqual(result["root_bdc_calls"], 9)
        self.assertEqual(result["root_seq_bdc_accepted"], 3)
        self.assertEqual(result["root_seq_bdc_proved"], 2)
        self.assertEqual(result["root_seq_bdc_selected_and_gain"], 6)
        self.assertEqual(result["root_comb_bdc_calls"], 0)

    def test_isf_time_is_disjoint_and_aggregated_by_phase(self):
        lines = [
            "stran-root experiment-time profile: schema=9 phase=seq scope=discovery total-sec=10 divisor-discovery-sec=2 resub-init-sec=1 resub-enum-sec=3 isf-portfolio-sec=3 unprofiled-sec=1.",
            "stran-root ISF time profile: schema=1 phase=seq portfolio-sec=2 rescue-core-sec=0.5 regular-core-sec=0.4 projection-sec=0.3 kit-synthesis-sec=0.2 bdc-synthesis-sec=0.1.",
            "stran-root ISF time profile: schema=1 phase=seq portfolio-sec=1 rescue-core-sec=0.2 regular-core-sec=0.1 projection-sec=0.1 kit-synthesis-sec=0.1 bdc-synthesis-sec=0.1.",
        ]
        result = parse_experiment_profile("\n".join(lines))
        self.assertEqual(result["profile_isf_portfolio_sec"], 3)
        self.assertEqual(result["profile_build_discovery_sec"], 9)
        self.assertAlmostEqual(result["root_isf_portfolio_sec"], 3)
        self.assertAlmostEqual(result["root_seq_isf_rescue_core_sec"], 0.7)
        self.assertAlmostEqual(result["root_seq_isf_regular_core_sec"], 0.5)
        self.assertAlmostEqual(result["root_seq_isf_projection_sec"], 0.4)
        self.assertAlmostEqual(result["root_seq_isf_kit_synthesis_sec"], 0.3)
        self.assertAlmostEqual(result["root_seq_isf_bdc_synthesis_sec"], 0.2)

    def test_tfo_core_value_profile_is_aggregated_by_phase(self):
        lines = [
            "stran-root TFO core-rescue profile: schema=3 phase=comb calls=0 skipped-no-extra=4 exact=0 rescued-roots=0 rescued-nodes=0 value-trials=0 value-exact=0 value-changed=0 value-unlocked=0 value-sec=0.000000.",
            "stran-root TFO core-rescue profile: schema=3 phase=seq calls=10 skipped-no-extra=3 exact=8 rescued-roots=4 rescued-nodes=6 value-trials=7 value-exact=3 value-changed=2 value-unlocked=1 value-sec=0.125000.",
            "stran-root TFO core-rescue profile: schema=3 phase=seq calls=6 skipped-no-extra=2 exact=5 rescued-roots=3 rescued-nodes=4 value-trials=4 value-exact=2 value-changed=1 value-unlocked=0 value-sec=0.075000.",
        ]
        result = parse_experiment_profile("\n".join(lines))
        self.assertEqual(result["root_tfo_core_calls"], 16)
        self.assertEqual(result["root_seq_tfo_core_rescued_nodes"], 10)
        self.assertEqual(result["root_seq_tfo_core_value_trials"], 11)
        self.assertEqual(result["root_seq_tfo_core_value_changed"], 3)
        self.assertEqual(result["root_seq_tfo_core_value_unlocked"], 1)
        self.assertAlmostEqual(result["root_seq_tfo_core_value_sec"], 0.2)
        self.assertEqual(result["root_comb_tfo_core_skipped_no_extra"], 4)


if __name__ == "__main__":
    unittest.main()
