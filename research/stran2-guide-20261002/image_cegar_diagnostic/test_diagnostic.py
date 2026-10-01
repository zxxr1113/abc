#!/usr/bin/env python3
"""Small exhaustive domains and optional real model-helper integration."""
import itertools
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import diagnostic as d

p=d.load_runtime(Path(__file__).resolve().parent.parent)


class Circuit:
    def __init__(self,ni,nl,gates,latches,outputs):
        self.ni,self.nl,self.gates,self.latches,self.outputs=ni,nl,gates,latches,outputs
        self.initial=[0]*nl;self.m=ni+nl+len(gates);self.na=len(gates);self.no=len(outputs)
    def step(self,x,s):
        v=[0]+list(x)+list(s)
        for a,b in self.gates:v.append((v[a//2]^(a&1))&(v[b//2]^(b&1)))
        lit=lambda l:v[l//2]^(l&1)
        return [lit(x) for x in self.outputs],[lit(x) for x in self.latches],v


class Tests(unittest.TestCase):
    def test_exhaustive_frame_maps_and_literal_polarities(self):
        fixtures=[Circuit(1,1,[(2,5),(7,1)],[3],[8]),
                  Circuit(0,1,[(2,1),(3,1)],[3],[4,6]),
                  Circuit(1,0,[(2,1),(3,1),(2,3)],[],[4,6,8]),
                  Circuit(0,0,[(1,1),(0,1)],[],[2,4])]
        for a in fixtures:
            g,base,step,reset=p.compile_graph(a);roles,vs=d.projected_pis(g,base,step,a)
            for bits in itertools.product((0,1),repeat=len(vs)):
                values=d.graph_values(g,vs,list(bits));u=list(bits[:a.ni]);s=list(bits[a.ni:a.ni+a.nl]);x=list(bits[a.ni+a.nl:])
                mapped=lambda mm:[values[l//2]^(l&1) for l in mm]
                self.assertEqual(mapped(base),a.step(u,s)[2])
                self.assertEqual(mapped(step),a.step(x,a.step(u,s)[1])[2])
                self.assertEqual(mapped(reset),a.step(x,a.initial)[2])

    def test_independent_current_inputs_required(self):
        a=Circuit(1,1,[(2,5)],[2],[6]);g,b,s,r=p.compile_graph(a)
        c=dict(root=3,recipe=[],out=0);m=s[3]
        roles,vs=d.projected_pis(g,b,s,a)
        row,values=d.replay_model(a,g,roles,vs,[0,1,1],c,m,"image",p.recipe_eval)
        self.assertEqual((row["previous_inputs"],row["current_inputs"],row["successor_state"]),([0],[1],[0]))
        self.assertFalse(row["reachable_teacher"])
        with self.assertRaises(ValueError): d.replay_model(a,g,roles,vs,[1,1,0],c,m,"image",p.recipe_eval)
        bad=dict(roles);bad["current_inputs"]=roles["previous_inputs"]
        with self.assertRaises(ValueError): d.replay_model(a,g,bad,vs,[0,1,1],c,m,"image",p.recipe_eval)

    def test_unreachable_image_never_reset_teacher(self):
        a=Circuit(0,1,[],[2],[2]);g,b,s,r=p.compile_graph(a);roles,vs=d.projected_pis(g,b,s,a)
        c=dict(root=1,recipe=[],out=0)
        row,_=d.replay_model(a,g,roles,vs,[1],c,s[1],"image",p.recipe_eval)
        self.assertEqual(row["previous_state"],[1]);self.assertFalse(row["reachable_teacher"])
        self.assertEqual(a.step([],a.initial)[1],[0])
        with self.assertRaises(ValueError): d.replay_model(a,g,roles,vs,[1],c,r[1],"reset",p.recipe_eval)
        with self.assertRaises(ValueError): d.replay_model(a,g,roles,vs,[1],c,s[1],"free",p.recipe_eval)

    def test_bad_model_and_source_miter_rejected(self):
        a=Circuit(1,1,[(2,5)],[2],[6]);g,b,s,r=p.compile_graph(a);roles,vs=d.projected_pis(g,b,s,a)
        c=dict(root=3,recipe=[],out=0)
        for bits in ([0,1],[0,1,2],[0,1,True]):
            with self.assertRaises(ValueError): d.replay_model(a,g,roles,vs,bits,c,s[3],"image",p.recipe_eval)
        with self.assertRaises(ValueError): d.replay_model(a,g,roles,vs,[0,1,1],c,s[3]^1,"image",p.recipe_eval)
        with self.assertRaises(ValueError): d.replay_model(a,g,roles,vs,[0,1,1],dict(c,out=6),s[3],"image",p.recipe_eval)

    def test_exhaustive_image_valid_class_preservation(self):
        # q1'=q2'=u: x&q1 equals x&q2 on reset+image, but not all states.
        a=Circuit(1,2,[(2,4)],[2,2],[8]);recipe=[2,6]
        samples=[a.step([x],a.step([u],[q1,q2])[1])[2]
                 for u,q1,q2,x in itertools.product((0,1),repeat=4)]
        samples += [a.step([x],[0,0])[2] for x in (0,1)]
        for v in samples:self.assertEqual(v[4],p.recipe_eval(recipe,-2,v))
        seq,mask=d.append_samples([0]*(a.m+1),1,samples)
        self.assertEqual(seq[4],p.recipe_eval(recipe,-2,seq,mask))
        self.assertTrue(any(a.step([x],[q1,q2])[2][4]!=p.recipe_eval(recipe,-2,a.step([x],[q1,q2])[2])
                            for x,q1,q2 in itertools.product((0,1),repeat=3)))

    def test_projection_keeps_target_and_pool(self):
        rows=[dict(root=2,pool=[1])];seq=[0,0,0]
        result=d.projection_counts(rows,seq,1,[[0,0,1],[0,1,1],[0,0,1]])[0]
        self.assertEqual(result["ordered_projection_nodes"],[2,1])
        self.assertEqual(result["learned_new_unique"],2)
        self.assertEqual(result["duplicate_learned_projection_rows"],1)

    @unittest.skipUnless(os.environ.get("STRAN2_MODEL_SOLVER"),"set STRAN2_MODEL_SOLVER for integration")
    def test_real_helper_sat_unsat_polarity_and_current_pi(self):
        a=Circuit(1,1,[(2,5)],[2],[6]);g,b,s,r=p.compile_graph(a);roles,vs=d.projected_pis(g,b,s,a)
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp);g.cnf(out/"g.cnf")
            queries=[s[3],s[3]^1,0,1]
            (out/"q").write_text("4\n"+"".join(f"{i} 1 {m}\n" for i,m in enumerate(queries)))
            (out/"v").write_text(str(len(vs))+"\n"+" ".join(map(str,vs))+"\n")
            subprocess.run([os.environ["STRAN2_MODEL_SOLVER"],str(out/"g.cnf"),str(out/"q"),str(out/"v"),str(out/"r"),str(out/"m")],check=True)
            models=[json.loads(x) for x in (out/"m").read_text().splitlines()]
            self.assertEqual([m["query"] for m in models],[0,1,3])
            for m in models:
                values=d.graph_values(g,vs,m["values"]);lit=queries[m["query"]]
                self.assertEqual(values[lit//2]^(lit&1),1)
            row,_=d.replay_model(a,g,roles,vs,models[0]["values"],dict(root=3,recipe=[],out=0),s[3],"image",p.recipe_eval)
            self.assertNotEqual(row["previous_inputs"],row["current_inputs"])


if __name__=="__main__": unittest.main()
