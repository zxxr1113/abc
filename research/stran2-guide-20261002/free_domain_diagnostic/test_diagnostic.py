import copy
import importlib.util
from pathlib import Path
import tempfile
import unittest
from diagnostic import append_worlds, choose_models, random_worlds, domain_diagnostics, worlds, digest
from independent import Aig

FROZEN=Path('/tmp/image-cegar-diagnostic-v1/source/diagnostic.py')
spec=importlib.util.spec_from_file_location('original_diagnostic_for_tests',FROZEN)
d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d)
p=d.load_runtime(Path('/tmp/nonlinear-anytime-pilot-v1/source'))

class Fixture:
    ni,nl,m,na,no=2,2,7,3,2
    initial=[0,0]
    gates=[(2,4),(2,6),(12,4)]
    latches=[2,2]
    outputs=[10,14]
    def step(self,inputs,state):
        values=[0]+list(inputs)+list(state)
        def lit(x): return values[x//2]^(x&1)
        for x,y in self.gates: values.append(lit(x)&lit(y))
        return [lit(x) for x in self.outputs],[lit(x) for x in self.latches],values

class Tests(unittest.TestCase):
    def test_previous_current_and_prededup_order(self):
        rows=[dict(query=0,previous_inputs=[0],current_inputs=[1],previous_state=[1],successor_state=[0]),
              dict(query=1,previous_inputs=[1],current_inputs=[0],previous_state=[1],successor_state=[0]),
              dict(query=2,previous_inputs=[0],current_inputs=[1],previous_state=[1],successor_state=[0])]
        initial=[dict(inputs=[0],state=[0])]
        b=choose_models(rows,initial,'previous_inputs');c=choose_models(rows,initial,'current_inputs')
        self.assertEqual([w['inputs'] for w in b],[[0],[1]])
        self.assertEqual([w['inputs'] for w in c],[[1],[0]])
        self.assertEqual([w['source_model_index'] for w in b],[0,1])
        self.assertEqual([w['state'] for w in b],[[1],[1]])
        self.assertEqual(len(choose_models(rows,initial,'current_inputs',cap=1)),1)

    def test_dedup_initial_and_empty_models(self):
        row=dict(query=0,previous_inputs=[1],current_inputs=[0],previous_state=[1])
        self.assertEqual(choose_models([row],[dict(inputs=[1],state=[1])],'previous_inputs'),[])
        self.assertEqual(choose_models([],[],'current_inputs'),[])

    def test_control_count_and_shared_prefix(self):
        initial=[dict(inputs=[0,0],state=[0,0])]
        r=random_worlds(2,2,9,2026100213,initial)
        self.assertEqual(r[:4],random_worlds(2,2,4,2026100213,initial))
        self.assertEqual(len({tuple(w['inputs']+w['state']) for w in r}),9)
        self.assertNotIn((0,0,0,0),{tuple(w['inputs']+w['state']) for w in r})
        self.assertEqual(random_worlds(2,2,0,1,initial),[])

    def test_frozen_sequence_and_witness_lane(self):
        a=Fixture();g,base,step,reset=p.compile_graph(a);cfg=p.Config(lanes=32)
        (free,image,initial),mask=p.signatures(g,[base,step,reset],cfg)
        seq=[i|(r<<32) for i,r in zip(image,initial)];sm=(1<<64)-1;seqcopy=copy.deepcopy(seq)
        before,_=p.search_root(p.Structure(a),7,[1,2,4],{},seq,sm,free,mask,cfg,p.Deadline(5))
        extended,em=append_worlds(a,free,mask,[dict(inputs=[1,1],state=[0,1])])
        after,_=p.search_root(p.Structure(a),7,[1,2,4],{},seq,sm,extended,em,cfg,p.Deadline(5))
        self.assertEqual(seq,seqcopy);self.assertTrue(before)
        self.assertEqual(before,after)
        self.assertEqual([x&mask for x in extended],free)
        self.assertEqual(em.bit_length(),33)

    def test_initial_free_filter_can_hide_qualified_identity(self):
        a=Fixture();g,base,step,reset=p.compile_graph(a);cfg=p.Config(lanes=32)
        (_,image,initial),mask=p.signatures(g,[base,step,reset],cfg)
        seq=[i|(r<<32) for i,r in zip(image,initial)];sm=(1<<64)-1
        before,stats=p.search_root(p.Structure(a),7,[1,2,4],{},seq,sm,image,mask,cfg,p.Deadline(5))
        expanded,em=append_worlds(a,image,mask,[dict(inputs=[1,1],state=[0,1])])
        after,_=p.search_root(p.Structure(a),7,[1,2,4],{},seq,sm,expanded,em,cfg,p.Deadline(5))
        self.assertEqual(before,[]);self.assertGreater(stats['no_sampled_free_witness'],0);self.assertTrue(after)
        for c in after:
            self.assertEqual(p.recipe_eval(c['recipe'],c['out'],image,mask),image[c['root']])
            self.assertEqual(c['witness_lane'],32)
            self.assertEqual(p.recipe_eval(c['recipe'],c['out'],seq,sm),seq[c['root']])
            self.assertGreater(c['conservative_gain'],0)

    def test_identical_empty_arm_domain_and_initial_identity(self):
        a=Fixture();g,base,step,reset=p.compile_graph(a);cfg=p.Config(lanes=32)
        (free,image,initial),mask=p.signatures(g,[base,step,reset],cfg)
        copied,cm=append_worlds(a,free,mask,[])
        self.assertEqual((copied,cm),(free,mask));self.assertIsNot(copied,free)
        self.assertEqual(digest(dict(free=free,mask=mask)),digest(dict(free=copied,mask=cm)))
        self.assertEqual(len(worlds(free,a.ni,a.nl,32)),32)

    def test_known_image_is_finite_membership_not_reachability(self):
        rows=[dict(inputs=[1],state=[0]),dict(inputs=[0],state=[1])]
        r=domain_diagnostics(rows,{(1,)},[0])
        self.assertEqual(r['reset_state_fraction'],0.5)
        self.assertEqual(r['known_sampled_image_state_fraction'],0.5)
        self.assertIsNone(domain_diagnostics([],set(),[0])['reset_state_fraction'])

    def test_independent_binary_decoder(self):
        with tempfile.TemporaryDirectory() as tmp:
            f=Path(tmp)/'small.aig';f.write_bytes(b'aig 3 1 1 1 1\n2\n6\n'+bytes([2,2]))
            a=Aig(f)
            for x in (0,1):
                for q in (0,1):
                    v=a.values([x],[q]);self.assertEqual(v,[0,x,q,x&q]);self.assertEqual(a.successor(v),[x])

if __name__=='__main__': unittest.main()
