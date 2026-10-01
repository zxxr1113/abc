import importlib
from pathlib import Path
import tempfile
import unittest
from audit_products import independent_product
from independent import Aig
from test_diagnostic import Fixture,p

class ProductTests(unittest.TestCase):
    def test_independent_product_checks_substitutions_not_free_equivalence(self):
        product=importlib.import_module('product');a=Fixture()
        c=dict(root=7,recipe=[10,8],out=-2)
        with tempfile.TemporaryDirectory() as tmp:
            tmp=Path(tmp);original=tmp/'original.aig';output=tmp/'product.aig'
            product.write_aig(original,product.rebuild(a,[]));product.write_aig(output,product.rebuild(a,[c]))
            self.assertEqual(independent_product(Aig(original),[c],output)['status'],'PASS')
            # Omitting the selected recipe must expose free-state disagreements.
            with self.assertRaisesRegex(ValueError,'CO replay differs'):
                independent_product(Aig(original),[],output)

    def test_independent_witness_rejects_missing_difference(self):
        from independent import witness
        product=importlib.import_module('product');a=Fixture();c=dict(root=7,recipe=[10,8],out=-2)
        with tempfile.TemporaryDirectory() as tmp:
            f=Path(tmp)/'a.aig';product.write_aig(f,product.rebuild(a,[]));ia=Aig(f)
            self.assertTrue(witness(ia,c,dict(inputs=[1,1],state=[0,1],root=0,replacement=1,lane=256)))
            with self.assertRaises(AssertionError):
                witness(ia,c,dict(inputs=[1,1],state=[1,1],root=1,replacement=1,lane=256))

if __name__=='__main__':unittest.main()
