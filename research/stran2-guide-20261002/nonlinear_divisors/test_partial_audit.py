#!/usr/bin/env python3
"""Prefix completeness tests; original evidence is never modified."""
from pathlib import Path
import tempfile
import unittest

from audit_partial import certificate_indices, read_complete_prefix


class PartialPrefixTests(unittest.TestCase):
    def rows(self, body, count=9):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "results.csv"
            p.write_text("query,result,conflicts,wall_s\n" + body)
            return read_complete_prefix(p, count)

    def test_complete_triples_only(self):
        rows, dropped = self.rows("0,1,0,0\n1,-1,0,0\n2,-1,0,0\n3,1,0,0\n4,-1,0,0\n")
        self.assertEqual(certificate_indices(rows), [0])
        self.assertEqual(dropped, 0)

    def test_unterminated_tail_is_not_certificate(self):
        rows, dropped = self.rows("0,1,0,0\n1,-1,0,0\n2,-1,0,0")
        self.assertEqual(len(rows), 2)
        self.assertEqual(certificate_indices(rows), [])
        self.assertGreater(dropped, 0)

    def test_unknown_or_sat_relation_rejected(self):
        for triple in ([0, -1, -1], [1, 0, -1], [1, -1, 0], [1, 1, -1], [1, -1, 1]):
            rows, _ = self.rows("".join(f"{i},{answer},0,0\n" for i, answer in enumerate(triple)))
            self.assertEqual(certificate_indices(rows), [])

    def test_prefix_order_and_ranges_strict(self):
        for body, count in [("1,1,0,0\n", 9), ("0,1,0,0\n0,-1,0,0\n", 9),
                            ("0,1,0,0\n", 0), ("0,2,0,0\n", 9),
                            ("0,1,-1,0\n", 9), ("0,1,0,nan\n", 9),
                            ("0,1,0,-1\n", 9), ("0,1,0\n", 9)]:
            with self.assertRaises(ValueError):
                self.rows(body, count)


if __name__ == "__main__":
    unittest.main()
