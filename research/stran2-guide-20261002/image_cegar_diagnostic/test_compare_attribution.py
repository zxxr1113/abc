import json
from pathlib import Path
import tempfile
import unittest
from compare_attribution import compare, stats


class Tests(unittest.TestCase):
    def test_equal_case_and_weighted_delta_are_distinct(self):
        rows=[dict(loaded_and=100,baseline_gain=2,refined_gain=5,delta_gain=3),
              dict(loaded_and=1000,baseline_gain=10,refined_gain=1,delta_gain=-9)]
        r=stats(rows)
        self.assertEqual(r['delta']['and_gain'],-6)
        self.assertAlmostEqual(r['delta']['equal_case_percent'],1.05)
        self.assertAlmostEqual(r['delta']['weighted_percent'],-600/1100)
        self.assertAlmostEqual(r['refined']['equal_case_percent']-r['baseline']['equal_case_percent'],r['delta']['equal_case_percent'])

    def test_empty_size_stratum_not_zero_percent(self):
        r=stats([])
        self.assertEqual(r['cases'],0)
        self.assertIsNone(r['delta']['equal_case_percent'])
        self.assertIsNone(r['delta']['weighted_percent'])

    def fixtures(self,root):
        dirs=[root/'old',root/'new']
        for d in dirs:
            (d/'source').mkdir(parents=True)
            (d/'integrity.json').write_text(json.dumps(dict(status='PASS')))
            for name in ('audit_online_products.py','audit_products.py','diagnostic.py','hash_direct_audit.py'):
                (d/'source'/name).write_text('identical')
        return dirs

    def test_policy_mismatch_rejected(self):
        with tempfile.TemporaryDirectory()as tmp:
            a,b=self.fixtures(Path(tmp));(b/'source/hash_direct_audit.py').write_text('different')
            with self.assertRaisesRegex(ValueError,'policy differs'):compare(a,b)

    def test_unpaired_cohort_rejected(self):
        with tempfile.TemporaryDirectory()as tmp:
            a,b=self.fixtures(Path(tmp))
            (a/'results.json').write_text(json.dumps([dict(case='a')]))
            (b/'results.json').write_text(json.dumps([dict(case='b')]))
            with self.assertRaisesRegex(ValueError,'cohort differs'):compare(a,b)


if __name__=='__main__':unittest.main()
