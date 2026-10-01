#!/usr/bin/env python3
"""Frozen same-pair-care SOP/AIG3 completion comparison; offline only."""
import argparse
from collections import Counter
import csv
import functools
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import time
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'seq_care_synthesis'))
from scan_exact_care import Aiger,synth,vars_tt
import guide
D=Path(__file__).resolve().parent
CUT_K=6;CUT_CAP=8;LANES=512
class Graph:
    def __init__(self):self.gates=[None];self.hash={}
    def pi(self):r=2*len(self.gates);self.gates.append(None);return r
    def land(self,a,b):
        if a==0 or b==0:return 0
        if a==1:return b
        if b==1:return a
        if a==b:return a
        if a==b^1:return 0
        if a>b:a,b=b,a
        if (a,b) not in self.hash:
            self.hash[a,b]=2*len(self.gates);self.gates.append((a,b))
        return self.hash[a,b]
    def xor(self,a,b):return self.land(self.land(a,b^1)^1,self.land(a^1,b)^1)^1
    def random_sim(self):
        rng=random.Random(2026100111);mask=(1<<LANES)-1;values=[0]
        for gate in self.gates[1:]:
            if gate is None:values.append(rng.getrandbits(LANES))
            else:
                a,b=gate;values.append((values[a//2]^(mask if a&1 else 0))&(values[b//2]^(mask if b&1 else 0)))
        return values,mask
    def cnf(self,path):
        count=1+3*sum(g is not None for g in self.gates)
        with path.open('w') as f:
            f.write(f'{len(self.gates)} {count}\n1 1\n')
            for i,gate in enumerate(self.gates):
                if gate is None:continue
                a,b=gate;z=2*i
                f.write(f'3 {a^1} {b^1} {z}\n2 {a} {z^1}\n2 {b} {z^1}\n')
        return count

def compile_graph(a):
    g=Graph();base=[0]+[g.pi() for _ in range(a.ni+a.nl)]
    for x,y in a.gates:base.append(g.land(base[x//2]^(x&1),base[y//2]^(y&1)))
    now=[g.pi() for _ in range(a.ni)]
    step=[0]+now+[base[x//2]^(x&1) for x in a.latches]
    reset=[0]+now+[0]*a.nl
    for x,y in a.gates:
        step.append(g.land(step[x//2]^(x&1),step[y//2]^(y&1)))
        reset.append(g.land(reset[x//2]^(x&1),reset[y//2]^(y&1)))
    return g,base,step,reset

def run_queries(g,queries,out,tag,solver):
    cnf=out/f'{tag}.cnf';qfile=out/f'{tag}.queries';result=out/f'{tag}.results.csv'
    clauses=g.cnf(cnf)
    with qfile.open('w') as f:
        f.write(f'{len(queries)}\n')
        for i,qs in enumerate(queries):f.write(f'{i} {len(qs)} '+' '.join(map(str,qs))+'\n')
    start=time.monotonic()
    with (out/f'{tag}.solver.log').open('w') as log:
        proc=subprocess.run([str(solver),str(cnf),str(qfile),str(result)],stdout=log,stderr=subprocess.STDOUT,check=True)
    rr=list(csv.DictReader(result.open()));assert len(rr)==len(queries)
    assert [int(r['query']) for r in rr]==list(range(len(queries)))
    answers=[int(r['result']) for r in rr];assert all(x in (-1,0,1) for x in answers)
    return answers,dict(queries=len(queries),statuses=dict(Counter(map(str,answers))),conflicts=sum(int(r['conflicts']) for r in rr),process_wall_s=time.monotonic()-start,solve_wall_s=sum(float(r['wall_s']) for r in rr),variables=len(g.gates),clauses=clauses)

def observed(a,b,mask):
    return int(bool((a^mask)&(b^mask)))|2*int(bool(a&(b^mask)))|4*int(bool((a^mask)&b))|8*int(bool(a&b))

def mffc_nodes(a,root,refs):
    rr={};todo=[root];result=set();nci=a.ni+a.nl
    while todo:
        i=todo.pop()
        if i<=nci:continue
        result.add(i)
        for l in a.gates[i-nci-1]:
            v=l//2;rr[v]=rr.get(v,refs[v])-1
            if rr[v]==0:todo.append(v)
    return result

def diagnose(c,out,solver,mode):
    assert mode in ("sop","aig3")
    from completion import choose,STATS
    start=time.monotonic();a=Aiger(c['input']);assert guide.sha(c['input'])==c['input_sha256'];nci=a.ni+a.nl
    refs=[0]*(a.m+1)
    for x,y in a.gates:refs[x//2]+=1;refs[y//2]+=1
    for x in a.outputs+a.latches:refs[x//2]+=1
    support=[0]+[1<<(i-1) for i in range(1,nci+1)]
    for x,y in a.gates:support.append(support[x//2]|support[y//2])
    g,base,step,reset=compile_graph(a);values,mask=g.random_sim()
    def sim(l):return values[l//2]^(mask if l&1 else 0)
    sfree=[sim(l) for l in base];sstep=[sim(l) for l in step];sreset=[sim(l) for l in reset]
    cuts=[[]]+[[(i,)] for i in range(1,nci+1)]
    work=[];pair_specs={};pair_checks=0;eligible=0;eligible_mffc_sum=0;full_ci_old=0;eligible_cut_roots=0
    for root in range(nci+1,a.m+1):
        x,y=a.gates[root-nci-1]
        merged={tuple(sorted(set(u)|set(v))) for u in cuts[x//2] for v in cuts[y//2] if len(set(u)|set(v))<=CUT_K}
        nodes=mffc_nodes(a,root,refs);nm=len(nodes)
        positions={x:i for i,x in enumerate(sorted(nodes))}
        @functools.lru_cache(None)
        def sub(i):
            if i not in nodes:return 0
            x,y=a.gates[i-nci-1];return (1<<positions[i])|sub(x//2)|sub(y//2)
        def removable(leaves):
            blocked=0
            for v in leaves:blocked|=sub(v)
            return nm-blocked.bit_count()
        ranked=sorted(merged,key=lambda leaves:(-removable(leaves),len(leaves),leaves))[:CUT_CAP]
        cuts.append([(root,),*ranked])
        if nm<2 or support[root]>>a.ni==0:continue
        eligible+=1;eligible_mffc_sum+=nm;full_ci_old+=support[root].bit_count()<=6
        chosen=[leaves for leaves in ranked if 2<=len(leaves)<=CUT_K and removable(leaves)>=2]
        eligible_cut_roots+=bool(chosen)
        for leaves in chosen:
            work.append((root,leaves,removable(leaves),nm))
            for u,v in itertools.combinations(leaves,2):
                pair_checks+=1
                if (u,v) in pair_specs:continue
                free=observed(sfree[u],sfree[v],mask)
                seq=observed(sstep[u],sstep[v],mask)|observed(sreset[u],sreset[v],mask)
                missing=free&~seq&15
                # A sampled free-state witness justifies targeting this pattern;
                # no missing pattern becomes care without both UNSAT queries.
                pair_specs[u,v]=missing
        if root%1000==0:guide.write_json(out/'progress.json',dict(stage='cuts',root=root,ands=a.na,cut_roots=eligible_cut_roots,cut_count=len(work)))
    pair_specs={pair:bits for pair,bits in pair_specs.items() if bits}
    metrics=dict(mode=mode,file=c['file'],input=c['input'],input_sha256=c['input_sha256'],loaded_and=c['source_and'],input_and=c['input_and'],root_count=a.na,roots_mffc2_with_state=eligible,overlapping_mffc_sum=eligible_mffc_sum,old_full_ci6_roots=full_ci_old,cut_roots=eligible_cut_roots,cuts=len(work),pair_checks=pair_checks,targeted_pairs=len(pair_specs),targeted_patterns=sum(x.bit_count() for x in pair_specs.values()),cut_prepare_wall_s=time.monotonic()-start)
    guide.write_json(out/'coverage.json',metrics)
    queries=[];query_meta=[]
    for (u,v),bits in sorted(pair_specs.items()):
        for pattern in range(4):
            if not bits>>pattern&1:continue
            for phase,mp in [('reset',reset),('step',step)]:
                queries.append([mp[u]^int(not(pattern&1)),mp[v]^int(not(pattern&2))]);query_meta.append((u,v,pattern,phase))
    answers,qstats=run_queries(g,queries,out,'care',solver)
    proven={};phase_counts={phase:Counter() for phase in ['reset','step']}
    assert len(answers)%2==0
    for i in range(0,len(answers),2):
        u,v,pattern,_=query_meta[i]
        for j in [0,1]:phase_counts[query_meta[i+j][3]][str(answers[i+j])]+=1
        if answers[i]==-1 and answers[i+1]==-1:proven[u,v]=proven.get((u,v),0)|(1<<pattern)
    metrics.update(care_queries=qstats,phase_statuses={k:dict(v) for k,v in phase_counts.items()},proved_pair_constraints=sum(x.bit_count() for x in proven.values()))
    guide.write_json(out/'care_proofs.json',dict(metrics=metrics,query_order=query_meta,answers=answers,proven=[dict(u=u,v=v,forbidden=bits) for (u,v),bits in proven.items()]))
    possible={};constrained=0;constrained_roots=set();synth_trials=0
    for root,leaves,removed,nm in work:
        n=len(leaves);vv,tm=vars_tt(n);care=tm
        for j in range(n):
            for k in range(j):
                pair=tuple(sorted((leaves[k],leaves[j])));bits=proven.get(pair,0)
                if not bits:continue
                for pattern in range(4):
                    if bits>>pattern&1:
                        care&=~((vv[k] if pattern&1 else vv[k]^tm)&(vv[j] if pattern&2 else vv[j]^tm))
        if care==tm:continue
        constrained+=1;constrained_roots.add(root);memo={0:0,**dict(zip(leaves,vv))}
        def ev(l):
            i=l//2
            if i not in memo:
                assert i>nci,(root,leaves,i)
                x,y=a.gates[i-nci-1];memo[i]=ev(x)&ev(y)
            return memo[i]^(tm if l&1 else 0)
        truth=ev(2*root);recipe,outcode=synth(truth&care,care,list(leaves))
        if mode=="aig3":recipe,outcode=choose(truth,care,list(leaves),a,mffc_nodes(a,root,refs),(recipe,outcode))
        ng=len(recipe)//2;synth_trials+=1
        if ng==0 or ng>20:continue
        used={x//2 for x in recipe+[outcode] if x>=2}
        rnodes=mffc_nodes(a,root,refs)
        # Any used internal boundary is now referenced by the recipe and its
        # TFI cannot be removed. MFFC accounting must retain these subgraphs.
        protected=set();todo=[x for x in used if x in rnodes]
        while todo:
            v=todo.pop()
            if v in protected or v not in rnodes:continue
            protected.add(v);x,y=a.gates[v-nci-1];todo.extend([x//2,y//2])
        removable_count=len(rnodes-protected);gain=removable_count-ng
        if gain<=0:continue
        key=(root,tuple(recipe),outcode)
        possible.setdefault(key,dict(root=root,leaves=list(leaves),gates=ng,recipe=recipe,out=outcode,truth=str(truth),care=str(care),original_mffc=nm,retained_mffc_nodes=len(protected),removable=removable_count,conservative_gain=gain,root_ci_support=support[root].bit_count()))
    metrics.update(constrained_cuts=constrained,constrained_roots=len(constrained_roots),synthesis_trials=synth_trials,positive_recipes=len(possible),positive_roots=len({x[0] for x in possible}))
    candidates=list(possible.values());free_queries=[]
    for cand in candidates:
        built=[]
        def code(c):
            if c>=0:return base[c//2]^(c&1)
            z=-c-2;return built[z//2]^(z&1)
        for i in range(0,len(cand['recipe']),2):built.append(g.land(code(cand['recipe'][i]),code(cand['recipe'][i+1])))
        diff=g.xor(base[cand['root']],code(cand['out']));free_queries.append([diff])
    fans,fstats=run_queries(g,free_queries,out,'free',solver)
    selected={}
    for cand,answer in zip(candidates,fans):
        cand['free_sat']=answer
        if answer!=1:continue
        key=(-cand['conservative_gain'],cand['gates'],cand['recipe'],cand['out'],cand['leaves'])
        if cand['root'] not in selected or key<selected[cand['root']][0]:selected[cand['root']]=(key,cand)
    picked=[selected[r][1] for r in sorted(selected)]
    metrics.update(free_queries=fstats,noncomb_positive_recipes=sum(x==1 for x in fans),selected_roots=len(picked),overlapping_gain_potential=sum(c['conservative_gain'] for c in picked),selected_beyond_old_ci6=sum(c['root_ci_support']>6 for c in picked),wall_s=time.monotonic()-start,status='complete')
    metrics['completion_stats']=dict(STATS)
    guide.write_json(out/'result.json',dict(metrics=metrics,candidates=candidates,selected=picked))
    print(json.dumps(metrics),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--case',required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--solver',type=Path,required=True);p.add_argument('--mode',choices=['sop','aig3'],required=True);args=p.parse_args()
    rules=json.loads((D/'frozen_rules.json').read_text());c=next(c for c in rules['cases'] if c['file']==args.case)
    args.out.mkdir(parents=True,exist_ok=False);diagnose(c,args.out,args.solver,args.mode)
