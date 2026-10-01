#!/usr/bin/env python3
"""Fixed four-cell offline comparison; all area columns are overlapping potential."""
import collections,hashlib,json,random,statistics,sys
from pathlib import Path
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;P=D.parent;E=P.parent
sys.path.insert(0,str(E/'teacher_adaptive_tools'))
from teacher_bmc import Aiger
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def key(q):return q['root'],tuple(q['recipe']),q['out']
def evaluate(q,values,mask):
    built=[]
    def val(c):
        if c>=0:return values[c//2]^(mask if c&1 else 0)
        z=-c-2;return built[z//2]^(mask if z&1 else 0)
    for x,y in zip(q['recipe'][::2],q['recipe'][1::2]):built.append(val(x)&val(y))
    return val(q['out'])
def fkey(q):
    used=sorted({c//2 for c in q['recipe']+[q['out']]if c>=2});n=len(used);width=1<<n;mask=(1<<width)-1
    values={0:0,**{u:sum(((1<<(1<<j))-1)<<p for p in range(1<<j,width,2<<j))for j,u in enumerate(used)}}
    return q['root'],tuple(used),evaluate(q,values,mask)
def main():
    rules=read(D/'frozen_rules.json');run=Path(read(D/'run_identity.json')['path']);pair=Path(read(P/'run_identity.json')['path'])
    assert(run/'complete.json').exists();rows=[]
    labels=['pair_sop','pair_aig3','full_sop','full_aig3']
    for c in rules['cases']:
        stem=Path(c['file']).stem;data={};arms={}
        for label,path,mode in [('pair_sop',pair,'sop'),('pair_aig3',pair,'aig3'),('full_sop',run,'sop'),('full_aig3',run,'aig3')]:
            p=path/mode/stem
            if not(p/'outcome.json').exists():
                assert c['file']not in rules['eligible_files'];arms[label]=dict(status='source-full-timeout',potential=None,selected_roots=None,free_sat=None,positive_recipes=None,wall_s=None);continue
            o=read(p/'outcome.json')
            if not o['complete']:arms[label]=dict(status=o['status'],potential=None,selected_roots=None,free_sat=None,positive_recipes=None,wall_s=o['wall_s']);continue
            q=read(p/'diagnostic/result.json');data[label]=q
            arms[label]=dict(status='complete',potential=q['metrics']['overlapping_gain_potential'],selected_roots=len(q['selected']),
                             free_sat=sum(x['free_sat']==1 for x in q['candidates']),positive_recipes=len(q['candidates']),
                             wall_s=o['wall_s'],result=str(p/'diagnostic/result.json'),result_sha256=sha(p/'diagnostic/result.json'))
        row=dict(file=c['file'],family=c['family'],loaded_and=c['source_and'],input_and=c['input_and'],arms=arms)
        if len(data)==4:
            saved=read(Path(rules['full_sources'][c['file']]['diagnostic'])/'result.json')
            assert data['full_sop']['candidates']==saved['candidates']and data['full_sop']['selected']==saved['selected']
            pp,pa,fs,fa=[arms[x]['potential']for x in labels]
            row['delta']=dict(pair_completion=pa-pp,full_completion=fa-fs,full_image_sop=fs-pp,interaction=(fa-fs)-(pa-pp))
            row['zero_full_sop_opened']=arms['full_sop']['selected_roots']==0 and arms['full_aig3']['selected_roots']>0
            old=data['full_sop']['candidates'];oldkeys={key(q)for q in old};oldfunctions={fkey(q)for q in old}
            added=[q for q in data['full_aig3']['candidates']if q['free_sat']==1 and key(q)not in oldkeys]
            a=Aiger(c['input']);nci=a.ni+a.nl;mask=(1<<4096)-1;rng=random.Random(2026100153)
            values=[0]+[rng.getrandbits(4096)for _ in range(nci)]
            for x,y in a.gates:values.append((values[x//2]^(mask if x&1 else 0))&(values[y//2]^(mask if y&1 else 0)))
            oldbyroot=collections.defaultdict(list)
            for q in old:oldbyroot[q['root']].append((q,evaluate(q,values,mask)))
            worlds={};classifications=[]
            def world(bit):
                if bit not in worlds:
                    ci=[values[i]>>bit&1 for i in range(1,nci+1)];_,_,v=a.step(ci[:a.ni],ci[a.ni:]);worlds[bit]=v
                return worlds[bit]
            for q in added:
                if fkey(q)in oldfunctions:
                    classifications.append(dict(root=q['root'],recipe=q['recipe'],out=q['out'],status='same-explicit-support-function'));continue
                truth=evaluate(q,values,mask);rootdiff=truth^values[q['root']];compared=oldbyroot[q['root']]
                differences=[truth^t for _,t in compared]
                if rootdiff and all(differences):
                    bit=(rootdiff&-rootdiff).bit_length()-1;v=world(bit);assert evaluate(q,v,1)!=v[q['root']]
                    models=[]
                    for (oldq,_),diff in zip(compared,differences):
                        b=(diff&-diff).bit_length()-1;v=world(b);assert evaluate(q,v,1)!=evaluate(oldq,v,1)
                        models.append(dict(old_recipe=oldq['recipe'],old_out=oldq['out'],bit=b))
                    classifications.append(dict(root=q['root'],recipe=q['recipe'],out=q['out'],status='original-CI-witness-different-from-every-old',root_witness_bit=bit,comparisons=models))
                else:classifications.append(dict(root=q['root'],recipe=q['recipe'],out=q['out'],status='unresolved-by-simulation'))
            row['completion_novelty']=dict(new_exact_sat=len(added),counts=dict(collections.Counter(x['status']for x in classifications)),
                                           classifications=classifications,seed=2026100153,lanes=4096,scope='Witness-novel recipes, not a count of distinct new functions; same signatures remain unresolved.')
        else:row['delta']=None;row['zero_full_sop_opened']=None;row['completion_novelty']=None
        rows.append(row)
    groups={}
    for name,rr in [('all55',rows),('discovery35',[r for r in rows if r['family']=='discovery']),('holdout20',[r for r in rows if r['family']=='holdout'])]+[(name,[r for r in rows if lo<=r['loaded_and']<hi])for name,lo,hi in [('lt1k',0,1000),('1k10k',1000,10000),('ge10k',10000,10**30)]]:
        common=[r for r in rr if r['delta']is not None];total=sum(r['loaded_and']for r in common)
        groups[name]=dict(planned=len(rr),common=len(common),loaded_and_common=total,
            potential={l:dict(sum=sum(r['arms'][l]['potential']for r in common),equal_case_pct=statistics.mean([100*r['arms'][l]['potential']/r['loaded_and']for r in common])if common else None,
                              weighted_pct=100*sum(r['arms'][l]['potential']for r in common)/total if total else None)for l in labels},
            full_sop_zero_cases=sum(r['arms']['full_sop']['selected_roots']==0 for r in common),zero_full_sop_opened=[r['file']for r in common if r['zero_full_sop_opened']],
            states={l:dict(collections.Counter(r['arms'][l]['status']for r in rr))for l in labels},
            deltas={k:dict(sum=sum(r['delta'][k]for r in common),equal_case_pp=statistics.mean([100*r['delta'][k]/r['loaded_and']for r in common])if common else None)for k in ['pair_completion','full_completion','full_image_sop','interaction']})
    common=[r for r in rows if r['delta']is not None]
    loo=[dict(excluded=r['file'],full_completion_potential_delta=sum(x['delta']['full_completion']for x in common if x!=r),
              equal_case_pp=statistics.mean([100*x['delta']['full_completion']/x['loaded_and']for x in common if x!=r]))for r in common]
    out=dict(schema=1,status='PASS',scope='All potential columns are overlapping per-root retained-MFFC structural estimates, NOT committed Build gain. Independent free-SAT uses1000-conflict screening. No C transform matrix.',
             rules_sha256=sha(D/'frozen_rules.json'),script_sha256=sha(__file__),cases=rows,groups=groups,leave_one_out=loo,
             cost=dict(original_full_source_attempt_wall_s=1317.061650954187,reused_source_not_free=True,full_sop_cached_replay_wall_s=sum(r['arms']['full_sop']['wall_s']or 0 for r in rows),full_aig3_new_child_wall_s=sum(r['arms']['full_aig3']['wall_s']or 0 for r in rows)),
             limitations=['Five original full-image timeouts retained as null; no rerun or fallback.','One best completion/cut may discard another noncombinational function in favor of a cheaper combinational completion.','Bounded<=3 AND family under frozen local care only; zero result does not rule out larger AIG or broader care/search.'])
    p=D/'final_results.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(dict(groups=groups,cost=out['cost']),indent=2))
if __name__=='__main__':main()
