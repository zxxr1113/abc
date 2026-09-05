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


if __name__ == "__main__":
    unittest.main()
