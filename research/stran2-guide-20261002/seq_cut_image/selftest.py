#!/usr/bin/env python3
"""Exhaustive reset/step/current-PI and pattern-polarity checks."""
import argparse,itertools,json,sys
from pathlib import Path
from types import SimpleNamespace
sys.dont_write_bytecode=True
import diagnose as d
def main():
    p=argparse.ArgumentParser();p.add_argument('--solver',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();a.out.mkdir(exist_ok=False)
    # q0'=a, q1'=b, q2'=a XOR b. Every register pair has all four
    # step patterns; three-register odd parity is unreachable after reset.
    machine=SimpleNamespace(ni=2,nl=3,gates=[(2,5),(3,4),(13,15),(6,8)],latches=[2,4,17])
    g,base,step,reset=d.compile_graph(machine)
    pi=[i for i,x in enumerate(g.gates) if i and x is None]
    worlds=[]
    for bits in itertools.product((0,1),repeat=len(pi)):
        vv=[0]*len(g.gates)
        for x,b in zip(pi,bits):vv[x]=b
        for i,gate in enumerate(g.gates):
            if gate is not None:
                x,y=gate;vv[i]=(vv[x//2]^(x&1))&(vv[y//2]^(y&1))
        worlds.append(vv)
    plan=[];queries=[];expected=[];order=[]
    for leaves in [(3,4),(1,3),(3,4,5),(1,3,4,5),(3,4,5,9)]:
        for pattern in range(1<<len(leaves)):
            plan.append((leaves,pattern))
            for phase,mp in [('reset',reset),('step',step)]:
                qs=[mp[u]^int(not(pattern>>j&1)) for j,u in enumerate(leaves)];queries.append(qs)
                expected.append(1 if any(all(v[l//2]^(l&1) for l in qs)for v in worlds) else -1)
                order.append(dict(leaves=leaves,pattern=pattern,phase=phase,literals=qs))
    answers,stats=d.run_queries(g,queries,a.out,'exhaustive',a.solver)
    assert answers==expected,(answers,expected)
    proven=d.forbidden_from_answers(plan,answers)
    assert proven.get((3,4),0)==0 and proven.get((1,3),0)==0
    assert proven[(3,4,5)]==sum(1<<p for p in range(8) if p.bit_count()%2)
    assert d.forbidden_from_answers([((3,4,5),1),((3,4,5),2)],[-1,0,-1,1])=={}
    # Reconstruct sampled-image bitset independently from explicit worlds.
    mask=(1<<len(worlds))-1
    for mp in [base,step,reset]:
        sig=[sum((v[l//2]^(l&1))<<i for i,v in enumerate(worlds)) for l in mp]
        for leaves in [(3,4),(1,3),(3,4,5),(1,3,4,5),(3,4,5,9)]:
            explicit={sum((v[mp[u]//2]^(mp[u]&1))<<j for j,u in enumerate(leaves))for v in worlds}
            assert d.observed_cut(sig,leaves,mask)==sum(1<<x for x in explicit)
    out=dict(status='PASS',queries=len(queries),worlds=len(worlds),current_PI_independent=True,three_way_relation_invisible_to_all_pairs=True,unknown_never_forbidden=True,query_order=order,answers=answers,statistics=stats)
    (a.out/'result.json').write_text(json.dumps(out,indent=2)+'\n');print('synthetic PASS',len(queries),'queries')
if __name__=='__main__':main()
