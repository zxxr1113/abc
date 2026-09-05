import unittest

from analyze_stran2_report import distribution, number, relative_scorr


class ReportTests(unittest.TestCase):
    def row(self, key, scorr, elapsed, flow="scorr-stran"):
        return dict(file=key, input_sha256=key, scorr_status="PASS",
                    stran_status="PASS", dsec_status="SKIP", error="",
                    scorr_args="", flow=flow, scorr_time_ms=scorr,
                    scorr_user_ms=scorr, stran_time_ms=elapsed,
                    stran_user_ms=elapsed, pipeline_time_ms=elapsed,
                    pipeline_user_ms=elapsed, scorr_and=100, stran_and=90,
                    scorr_latches=10, stran_latches=10)

    def test_per_case_mean_not_ratio_of_sums(self):
        base = {"a": self.row("a", 1, 5), "b": self.row("b", 100, 200)}
        data = {"a": self.row("a", 0, 10, "stran2"),
                "b": self.row("b", 0, 200, "stran2")}
        result = relative_scorr(base, data, ["a", "b"], per_case=True)
        self.assertEqual(result["timing"]["time_ms"]["extra_ratio"]["mean"], 5)
        self.assertEqual(len(result["timing"]["time_ms"]["per_case"]), 2)

    def test_standalone_stran_does_not_subtract_again(self):
        base = {"a": self.row("a", 2, 10)}
        result = relative_scorr(base, base, ["a"])
        self.assertEqual(result["timing"]["time_ms"]["extra_ratio"]["mean"], 5)

    def test_negative_estimate_is_not_dropped(self):
        result = distribution([-0.5, 1.5])
        self.assertEqual(result["mean"], 0.5)
        self.assertEqual(result["negative"], 1)
        self.assertIsNone(result["geomean"])

    def test_invalid_reference_is_rejected(self):
        base = {"a": self.row("a", 0, 10)}
        with self.assertRaises(ValueError):
            relative_scorr(base, base, ["a"])
        base["a"]["scorr_time_ms"] = 1
        base["a"]["stran_status"] = "TIMEOUT"
        with self.assertRaises(ValueError):
            relative_scorr(base, base, ["a"])

    def test_nonfinite_is_not_a_measurement(self):
        with self.assertRaises(ValueError):
            number({"file": "a", "value": "nan"}, "value")


if __name__ == "__main__":
    unittest.main()
