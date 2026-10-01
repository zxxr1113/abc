import importlib
from pathlib import Path
import unittest

from diagnostic import load_runtime
from audit_global_alias_products import GlobalStructure, removal_set
p=load_runtime(Path(__file__).resolve().parent.parent)
product=importlib.import_module('product')


class Circuit:
    def __init__(self,ni,gates,outputs):
        self.ni,self.nl,self.gates,self.outputs=ni,0,gates,outputs
        self.latches=[];self.initial=[];self.m=ni+len(gates);self.na=len(gates);self.no=len(outputs)
    def step(self,x,s):
        v=[0]+list(x)
        for a,b in self.gates:v.append((v[a//2]^(a&1))&(v[b//2]^(b&1)))
        return [v[l//2]^(l&1)for l in self.outputs],[],v


def candidate(a,root,recipe,out,assignment):
    return dict(root=root,recipe=recipe,out=out,free_witness=dict(inputs=assignment,state=[]),**p.Structure(a).cost(root,recipe,out))


class Tests(unittest.TestCase):
    def test_later_id_alias_and_complement(self):
        a=Circuit(3,[(2,4),(8,6),(2,6)],[10,12]);g=GlobalStructure(p,a)
        c=candidate(a,5,[2,6],-2,[1,0,1]);r=g.classify(c)
        self.assertEqual(r['selected_original_alias_literal'],12)
        self.assertTrue(r['output_alias_is_later']);self.assertNotIn(5,r['output_alias_support'])
        self.assertEqual(r['global_live_fresh_gates'],0)
        c=candidate(a,5,[2,6],-3,[1,1,1]);r=g.classify(c)
        self.assertEqual(r['selected_original_alias_literal'],13)
        self.assertEqual(r['free_witness_alias_replay']['status'],'PASS')

    def test_two_gate_output_and_intermediate_aliases(self):
        a=Circuit(4,[(2,4),(10,6),(2,8),(14,4)],[12,16]);g=GlobalStructure(p,a)
        c=candidate(a,6,[2,8,-2,4],-4,[1,1,0,1]);r=g.classify(c)
        self.assertEqual(r['selected_original_alias_literal'],16)
        self.assertEqual(r['intermediate'][0]['safe_original_alias_literals'],[14])
        self.assertEqual(r['global_live_fresh_gates'],0)
        new=candidate(a,6,[2,8,-2,6],-4,[1,0,1,1]);r=g.classify(new)
        self.assertEqual(r['safe_original_alias_literals'],[])
        self.assertEqual(r['global_live_fresh_gates'],1)
        self.assertEqual(r['intermediate'][0]['later_safe_alias_literals'],[14])

    def test_root_dependent_only_alias_is_not_safe(self):
        a=Circuit(2,[(2,1),(6,4)],[6,8]);c=candidate(a,3,[2,4],-2,[1,0]);r=GlobalStructure(p,a).classify(c)
        self.assertEqual(r['original_alias_literals'],[8])
        self.assertEqual(r['safe_original_alias_literals'],[])
        self.assertEqual(r['classification'],'WHOLE_ORIGINAL_ALIAS_ROOT_DEPENDENT_ONLY')

    def test_dead_constructed_gate_not_global_fresh_output(self):
        a=Circuit(3,[(2,4),(8,6)],[10]);c=candidate(a,5,[4,6],2,[1,0,1]);r=GlobalStructure(p,a).classify(c)
        self.assertEqual(r['selected_original_alias_literal'],2)
        self.assertEqual(r['global_live_fresh_gates'],0)

    def test_demotion_preserves_exact_materialization(self):
        a=Circuit(3,[(2,4),(8,6),(2,6)],[10,12]);c=candidate(a,5,[2,6],-2,[1,0,1])
        built=product.rebuild(a,[c]);r=GlobalStructure(p,a).classify(c)
        self.assertTrue(built['realization'][0]['output_is_new'])
        new,demoted,without=removal_set([c],built['realization'],[r])
        self.assertEqual(new,[]);self.assertEqual(demoted,[c]);self.assertEqual(without,[c])
        self.assertEqual(product.rebuild(a,without),built)

    def test_novel_build_removal_does_not_reselect(self):
        a=Circuit(3,[(2,4),(8,6),(2,6)],[10,12]);c=candidate(a,5,[4,6],-2,[1,0,1])
        built=product.rebuild(a,[c]);r=GlobalStructure(p,a).classify(c)
        new,demoted,without=removal_set([c],built['realization'],[r])
        self.assertEqual(new,[c]);self.assertEqual(demoted,[]);self.assertEqual(without,[])
        self.assertEqual(len(product.rebuild(a,without)['gates'])-len(built['gates']),1)


if __name__=='__main__':unittest.main()
