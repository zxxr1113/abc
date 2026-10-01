#!/usr/bin/env python3
"""Diagnostic: exact one-step image+reset binary care, 6-CI roots, 16-input pair cone cap.
No sampled row certifies care. Exhaustive bit truth of free predecessor state and
free previous/current PI proves every removed pair combination unreachable.
"""
import concurrent.futures as cf
from functools import lru_cache
import json
from pathlib import Path
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'teacher_adaptive_tools'))
from teacher_bmc import Aiger
import guide

D=Path(__file__).resolve().parent
K=6
PAIR_CI_CAP=16

@lru_cache(None)
def vars_tt(n):
    bits=1<<n;mask=(1<<bits)-1
    return tuple(sum(((1<< (1<<j))-1) << p for p in range(1<<j,bits,2<<j)) for j in range(n)),mask

class Graph:
    def __init__(self):self.gates=[None];self.ci=[];self.support=[frozenset()];self.hash={}
    def pi(self):
        i=len(self.gates);self.gates.append(None);self.ci.append(i);self.support.append(frozenset([i]));return 2*i
    def land(self,a,b):
        if a==0 or b==0:return 0
        if a==1:return b
        if b==1:return a
        if a==b:return a
        if a==b^1:return 0
        if a>b:a,b=b,a
        if (a,b) in self.hash:return self.hash[a,b]
        r=2*len(self.gates);self.gates.append((a,b));self.support.append(self.support[a//2]|self.support[b//2]);self.hash[a,b]=r;return r
    def eval(self,lits,support=None):
        ss=sorted(set().union(*(self.support[x//2] for x in lits))) if support is None else support
        vv,mask=vars_tt(len(ss));memo={0:0,**{i:v for i,v in zip(ss,vv)}}
        def ev(l):
            i=l//2
            if i not in memo:
                a,b=self.gates[i];memo[i]=ev(a)&ev(b)
            return memo[i] ^ (mask if l&1 else 0)
        return [ev(x) for x in lits],mask

def compile_graph(a):
    g=Graph();base=[0]+[g.pi() for _ in range(a.ni+a.nl)]
    for x,y in a.gates:base.append(g.land(base[x//2]^(x&1),base[y//2]^(y&1)))
    nowpi=[g.pi() for _ in range(a.ni)]
    step=[0]+nowpi+[base[x//2]^(x&1) for x in a.latches]
    reset=[0]+nowpi+[0]*a.nl
    for x,y in a.gates:
        step.append(g.land(step[x//2]^(x&1),step[y//2]^(y&1)))
        reset.append(g.land(reset[x//2]^(x&1),reset[y//2]^(y&1)))
    return g,base,step,reset

def qm(on,dc,n):
    allterms={(x,0) for x in range(1<<n) if (on|dc)>>x&1};primes=set()
    while allterms:
        used=set();nxt=set()
        for x,m in allterms:
            for j in range(n):
                b=1<<j
                if not m&b and (x^b,m) in allterms:
                    used.add((x,m));nxt.add((x&~b,m|b))
        primes.update(allterms-used);allterms=nxt
    options=[]
    for x,m in primes:
        cover=sum(1<<v for v in range(1<<n) if (v&~m)==x)&on
        if cover:options.append((x,m,cover))
    selected=[];missing=on
    while missing:
        # Necessary prime first, then deterministic maximum new coverage/literal cost.
        essential=None
        for v in range(1<<n):
            if not missing>>v&1:continue
            opts=[q for q in options if q[2]>>v&1]
            if len(opts)==1:essential=opts[0];break
        q=essential or min(options,key=lambda q:(-((q[2]&missing).bit_count()/max(1,n-q[1].bit_count())),n-q[1].bit_count(),q[0],q[1]))
        selected.append(q[:2]);missing&=~q[2]
    return selected

def synth(on,care,leaves):
    n=len(leaves);mask=(1<<(1<<n))-1;best=None
    for flip in (0,1):
        target=(on^(care if flip else 0))&care
        cubes=qm(target,mask^care,n)
        recipe=[];hashes={}
        def land(a,b):
            if a==0 or b==0:return 0
            if a==1:return b
            if b==1:return a
            if a==b:return a
            if a==b^1:return 0
            a,b=sorted([a,b]);key=a,b
            if key not in hashes:
                hashes[key]=2*(len(leaves)+len(recipe)+1);recipe.append(key)
            return hashes[key]
        def tree(lits):
            if not lits:return 1
            while len(lits)>1:lits=[land(lits[i],lits[i+1]) if i+1<len(lits) else lits[i] for i in range(0,len(lits),2)]
            return lits[0]
        terms=[tree([2*(j+1)^int(not(x>>j&1)) for j in range(n) if not m>>j&1]) for x,m in cubes]
        out=(tree([x^1 for x in terms])^1)^flip
        if best is None or (len(recipe),out,recipe)<(len(best[0]),best[1],best[0]):best=recipe,out
    recipe,out=best
    def code(x):
        v=x//2
        if v==0:return x
        if v<=len(leaves):return 2*leaves[v-1]^(x&1)
        return -(2*(v-len(leaves)-1)+(x&1)+2)
    return [code(x) for gate in recipe for x in gate],code(out)

def analyze(c):
    start=time.monotonic();a=Aiger(c['input']);g,base,step,reset=compile_graph(a)
    refs=[0]*(a.m+1)
    for x,y in a.gates:refs[x//2]+=1;refs[y//2]+=1
    for x in a.outputs+a.latches:refs[x//2]+=1
    supports=[frozenset()]+[frozenset([i]) for i in range(1,a.ni+a.nl+1)]
    for x,y in a.gates:supports.append(supports[x//2]|supports[y//2])
    def mffc(root):
        rr={};todo=[root];count=0
        while todo:
            i=todo.pop()
            if i<=a.ni+a.nl:continue
            count+=1
            for l in a.gates[i-a.ni-a.nl-1]:
                v=l//2;rr[v]=rr.get(v,refs[v])-1
                if rr[v]==0:todo.append(v)
        return count
    @lru_cache(None)
    def relation(u,v):
        possible=0
        for phase in (step,reset):
            lits=[phase[u],phase[v]];ss=g.support[lits[0]//2]|g.support[lits[1]//2]
            if len(ss)>PAIR_CI_CAP:return 15
            (tu,tv),mask=g.eval(lits)
            for uv in range(4):
                hit=(tu if uv&1 else tu^mask)&(tv if uv&2 else tv^mask)
                if hit:possible|=1<<uv
        return possible
    rows=[];eligible=constrained=changed=0
    for root in range(a.ni+a.nl+1,a.m+1):
        leaves=sorted(supports[root]);n=len(leaves)
        if n<2 or n>K or not any(x>a.ni for x in leaves):continue
        nm=mffc(root)
        if nm<2:continue
        eligible+=1;tt,mask=g.eval([base[root]],[base[x]//2 for x in leaves]);on=tt[0];care=mask;clauses=[]
        vv,_=vars_tt(n)
        for j in range(n):
            if leaves[j]<=a.ni:continue
            for k in range(j):
                if leaves[k]<=a.ni:continue
                rel=relation(leaves[j],leaves[k])
                if rel==15:continue
                clauses.append(dict(u=leaves[j],v=leaves[k],possible=rel))
                for uv in range(4):
                    if rel>>uv&1:continue
                    care&=~((vv[j] if uv&1 else vv[j]^mask)&(vv[k] if uv&2 else vv[k]^mask))
        if care==mask:continue
        constrained+=1;recipe,out=synth(on&care,care,leaves)
        if len(recipe)//2<=0 or len(recipe)//2>=nm:continue
        temp=[]
        def value(x):
            if x>=0:return vv[leaves.index(x//2)]^(mask if x&1 else 0) if x//2 else (mask if x&1 else 0)
            l=-x-2;return temp[l//2]^(mask if l&1 else 0)
        for j in range(0,len(recipe),2):temp.append(value(recipe[j])&value(recipe[j+1]))
        val=value(out)
        assert not((val^on)&care)
        if val==on:continue
        changed+=1
        rows.append(dict(root=root,leaves=leaves,mffc=nm,gates=len(recipe)//2,recipe=recipe,out=out,truth=str(on),care=str(care),newtruth=str(val),constraints=clauses))
    result=dict(file=c['file'],input=c['input'],input_sha256=guide.sha(c['input']),nodes=a.m,eligible=eligible,constrained=constrained,changed=changed,pair_cache=relation.cache_info()._asdict(),wall_s=time.monotonic()-start,candidates=rows)
    guide.write_json(D/'diagnostic'/f'{Path(c["file"]).stem}.json',result)
    print(c['file'],eligible,constrained,changed,round(result['wall_s'],3),flush=True)
    return result

if __name__=='__main__':
    (D/'diagnostic').mkdir(exist_ok=False)
    cohort=guide.cases();guide.write_json(D/'diagnostic_plan.json',dict(cases=cohort,root_ci_cap=K,pair_ci_cap=PAIR_CI_CAP,care='all possible binary RO combinations in image of free predecessor state, union reset',synthesis='deterministic prime implicants, greedy cover, both polarities; new AIG <= mffc-1; not a proof/commit'))
    with cf.ProcessPoolExecutor(8) as p:rows=list(p.map(analyze,cohort))
    guide.write_json(D/'diagnostic_results.json',rows)
