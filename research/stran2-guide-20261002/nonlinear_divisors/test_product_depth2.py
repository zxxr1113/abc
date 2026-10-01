#!/usr/bin/env python3
"""The extra certificate cannot relabel shallow SAT or omit a reset obligation."""
import copy
import unittest

from product_depth2 import candidate_certificate_sha, certificate_kind


class TypedCertificateTests(unittest.TestCase):
    def candidate(self):
        c = dict(root=7, recipe=[4, 10], out=-2,
                 proof=dict(free="SAT", free_witness_replayed=True, reset="UNSAT", step="SAT"),
                 qualified_offline_opportunity=False)
        c["depth2_certificate"] = dict(schema=1, kind="RESET_PREFIX_IMAGE", depth=2,
            input_sha256="a" * 64, candidate_sha256=candidate_certificate_sha(c),
            reset_prefix=["UNSAT", "UNSAT"], unrestricted_image="UNSAT", free_witness_replayed=True,
            fresh_recheck="PASS", evidence_sha256={key: "b" * 64 for key in ("cnf", "queries", "results", "query_order")})
        return c

    def test_accepts_explicit_complete_depth2_preserves_old_status(self):
        c = self.candidate()
        old = copy.deepcopy(c)
        self.assertEqual(certificate_kind(c, "a" * 64), "RESET_PREFIX_IMAGE_2")
        self.assertEqual(c, old)
        self.assertEqual(c["proof"]["step"], "SAT")
        self.assertFalse(c["qualified_offline_opportunity"])

    def test_rejects_missing_wrong_or_unknown_obligation(self):
        bad = [("reset_prefix", ["UNSAT"]), ("reset_prefix", ["UNSAT", "SAT"]),
               ("reset_prefix", ["UNSAT", "UNKNOWN"]), ("unrestricted_image", "SAT"),
               ("unrestricted_image", "UNKNOWN"), ("depth", 3), ("depth", True),
               ("kind", "BOUNDED_BMC"), ("free_witness_replayed", False),
               ("fresh_recheck", "NOT_RUN"), ("evidence_sha256", {})]
        for key, value in bad:
            c = self.candidate()
            c["depth2_certificate"][key] = value
            with self.assertRaises(ValueError, msg=str((key, value))):
                certificate_kind(c, "a" * 64)

    def test_rejects_wrong_input_or_candidate_identity(self):
        c = self.candidate()
        with self.assertRaises(ValueError):
            certificate_kind(c, "c" * 64)
        c["recipe"] = [2, 10]
        with self.assertRaises(ValueError):
            certificate_kind(c, "a" * 64)

    def test_depth1_default_still_requires_all_three_results(self):
        c = self.candidate()
        del c["depth2_certificate"]
        with self.assertRaises(ValueError):
            certificate_kind(c, "a" * 64)
        c["proof"]["step"] = "UNSAT"
        c["qualified_offline_opportunity"] = True
        self.assertEqual(certificate_kind(c, "a" * 64), "RESET_IMAGE_1")
        c["proof"]["free"] = "UNKNOWN"
        with self.assertRaises(ValueError):
            certificate_kind(c, "a" * 64)


if __name__ == "__main__":
    unittest.main()
