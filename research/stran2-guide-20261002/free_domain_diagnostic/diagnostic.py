#!/usr/bin/env python3
"""One frozen free-witness-filter diagnostic; never an online integration."""
from __future__ import annotations
import argparse
from collections import Counter
import copy
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time
sys.dont_write_bytecode=True
from independent import Aig as IndependentAig, recipe as independent_recipe, witness as independent_witness

HERE=Path(__file__).resolve().parent

def require(c,m):
    if not c: raise ValueError(m)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(x): return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def read(p): return json.loads(Path(p).read_text())
def write(p,x):
    p=Path(p);t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(x,sort_keys=True,indent=2)+'\n');t.replace(p)
def cid(c): return c['root'],tuple(c['recipe']),c['out']
def clone_graph(p,g):
    new=p.Graph();new.gates=list(g.gates);new.hash=dict(g.hash);return new

def worlds(free, ni, nl, count):
    return [dict(inputs=[(free[i]>>lane)&1 for i in range(1,ni+1)],
                 state=[(free[i]>>lane)&1 for i in range(ni+1,ni+nl+1)]) for lane in range(count)]
def worldkey(w): return tuple(w['inputs']+w['state'])
def choose_models(models, initial, field, cap=256):
    require(field in ('previous_inputs','current_inputs'),'unknown PI frame')
    seen={worldkey(w) for w in initial};out=[]
    for i,row in enumerate(models):
        world=dict(inputs=list(row[field]),state=list(row['previous_state']),source_model_index=i,
                   source_query=row['query'],pi_field=field,domain='unrestricted_free_PI_RO')
        key=worldkey(world)
        if key in seen: continue
        seen.add(key);out.append(world)
        if len(out)==cap: break
    return out

def random_worlds(ni,nl,count,seed,initial):
    rng=random.Random(seed);seen={worldkey(w) for w in initial};out=[]
    require(count<=2**(ni+nl)-len(seen),'not enough distinct free worlds')
    while len(out)<count:
        w=dict(inputs=[rng.randrange(2) for _ in range(ni)],state=[rng.randrange(2) for _ in range(nl)],
               domain='unrestricted_free_PI_RO',uniform_index=len(out))
        key=worldkey(w)
        if key not in seen: seen.add(key);out.append(w)
    return out

def append_worlds(a,free,mask,extra):
    require(mask>=1 and mask&(mask+1)==0,'invalid mask')
    out=list(free);offset=mask.bit_length()
    for w in extra:
        values=a.step(w['inputs'],w['state'])[2]
        for node,value in enumerate(values): out[node]|=value<<offset
        offset+=1
    require(all((x&mask)==y for x,y in zip(out,free)),'initial witness lanes changed')
    return out,(1<<offset)-1

def domain_diagnostics(rows, known_image_states, reset):
    n=len(rows); nr=sum(w['state']==reset for w in rows)
    ni=sum(tuple(w['state']) in known_image_states for w in rows)
    return dict(count=n,reset_state_matches=nr,reset_state_fraction=nr/n if n else None,
                known_sampled_image_state_matches=ni,known_sampled_image_state_fraction=ni/n if n else None,
                interpretation='These matched states cannot witness a relation valid on reset/image, for any PI. Absence from this finite known-image set says nothing about image membership or reachability.')

def verify_saved_models(d,p,a,g,base,step,old,source,out,deadline,ia):
    root=source/'models';prov=read(root/'provenance.json');saved=read(root/'replayed_models.json')
    roles,variables=d.projected_pis(g,base,step,a)
    require(roles==prov['roles'],'saved model roles differ')
    failed=[c for c in old if c['proof']['step']=='SAT'];miters=[]
    for c in failed: miters.append(g.xor(step[c['root']],p.graph_recipe(g,step,c['recipe'],c['out'])))
    g.cnf(out/'models_reconstructed.cnf')
    qtext=str(len(miters))+'\n'+''.join(f'{i} 1 {m}\n' for i,m in enumerate(miters))
    vtext=str(len(variables))+'\n'+' '.join(map(str,variables))+'\n'
    require(sha(out/'models_reconstructed.cnf')==prov['cnf_sha256']==sha(root/'models.cnf'),'saved model CNF mismatch')
    require(qtext==(root/'models.queries').read_text() and sha(root/'models.queries')==prov['queries_sha256'],'model assumptions mismatch')
    require(vtext==(root/'models.variables').read_text() and sha(root/'models.variables')==prov['variables_sha256'],'model variable roles mismatch')
    expected_sources=[dict(query=i,phase='image',root=c['root'],recipe=c['recipe'],out=c['out'],miter=m) for i,(c,m) in enumerate(zip(failed,miters))]
    require(expected_sources==prov['query_sources'],'model candidate bindings mismatch')
    report=read(root/'report.json')
    for file,key in [('models.jsonl','models_sha256'),('results.csv','results_sha256'),('replayed_models.json','replayed_models_sha256')]:
        require(sha(root/file)==report[key],'model report binding mismatch')
    raw=[json.loads(s) for s in (root/'models.jsonl').read_text().splitlines()]
    answers=list(csv.DictReader((root/'results.csv').open()))
    require([int(r['query']) for r in answers]==list(range(len(failed))),'model result ordering')
    require([r['query'] for r in raw]==[int(r['query']) for r in answers if int(r['result'])==1],'model projection set')
    require(len(raw)==len(saved),'saved model count')
    samples=[];seen={}
    for model,row in zip(raw,saved):
        deadline.remaining();i=model['query']
        replay,values=d.replay_model(a,g,roles,variables,model['values'],failed[i],miters[i],'image',p.recipe_eval)
        replay.update(query=i,candidate_id=list(cid(failed[i])),source_provenance_sha256=sha(root/'provenance.json'))
        # JSON represents the identity's recipe tuple as a list.
        replay['candidate_id'][1]=list(replay['candidate_id'][1])
        key=tuple(replay['current_inputs']+replay['successor_state'])
        if key not in seen: seen[key]=len(samples);samples.append(values)
        replay['sample_index']=seen[key]
        require(replay==row,'saved replay differs from raw full model')
        pred=ia.values(row['previous_inputs'],row['previous_state'])
        require(ia.successor(pred)==row['successor_state'],'independent successor replay differs')
        independently=ia.values(row['current_inputs'],row['successor_state'])
        require(independently==values and independently[failed[i]['root']]!=independent_recipe(failed[i]['recipe'],failed[i]['out'],independently),'independent image witness replay failed')
    return saved,samples

def verify_saved_proofs(p,a,g,mappings,old,source,out,free,ia):
    candidates=read(source/'new_proofs/candidates.json');proofgraph=clone_graph(p,g);queries=[]
    for c in candidates:
        for _,mapping in mappings:
            queries.append([proofgraph.xor(mapping[c['root']],p.graph_recipe(proofgraph,mapping,c['recipe'],c['out']))])
    proofgraph.cnf(out/'old_proof_reconstructed.cnf');report=read(source/'new_proofs/report.json')
    qtext=str(len(queries))+'\n'+''.join(f'{i} 1 {q[0]}\n' for i,q in enumerate(queries))
    require(sha(out/'old_proof_reconstructed.cnf')==report['cnf_sha256'],'saved refined proof CNF mismatch')
    require(qtext==(source/'new_proofs/obligations.queries').read_text(),'saved refined proof assumptions mismatch')
    for name,key in [('obligations.cnf','cnf_sha256'),('obligations.queries','queries_sha256'),('obligations.results.csv','results_sha256')]:
        require(sha(source/'new_proofs'/name)==report[key],'saved refined proof receipt hash mismatch')
    raw=list(csv.DictReader((source/'new_proofs/obligations.results.csv').open()))
    require([int(x['query']) for x in raw]==list(range(len(queries))),'saved proof query order')
    names={1:'SAT',0:'UNKNOWN',-1:'UNSAT'};qualified={cid(c):c['qualified_offline_opportunity'] for c in old}
    for i,c in enumerate(candidates):
        statuses=[int(r['result']) for r in raw[3*i:3*i+3]]
        require(c['diagnostic_proof']==dict(zip(('free','reset','image'),map(names.get,statuses))),'saved refined proof status mismatch')
        require(c['qualified_offline_opportunity']==(statuses==[1,-1,-1]),'saved qualification mismatch')
        require(p.witness(a,c,free)==c['free_witness'],'saved free witness mismatch')
        independent_witness(ia,c,c['free_witness'],free)
        qualified[cid(c)]=c['qualified_offline_opportunity']
    return qualified

def proof_new(p,a,ia,candidates,free_by_arm,solver,out,deadline):
    out.mkdir();g,base,step,reset=p.compile_graph(a);queries=[];order=[];solver_hash=sha(solver)
    for i,c in enumerate(candidates):
        arm=c['first_discovery_arm'];free=free_by_arm[arm]
        c['free_witness']=p.witness(a,c,free);independent_witness(ia,c,c['free_witness'],free)
        for phase,mapping in [('free',base),('reset',reset),('image',step)]:
            miter=g.xor(mapping[c['root']],p.graph_recipe(g,mapping,c['recipe'],c['out']))
            order.append(dict(query=len(queries),candidate_index=i,candidate_id=list(cid(c)),phase=phase,assumptions=[miter]))
            queries.append([miter])
    write(out/'query_order.json',order)
    if candidates:
        ans,report=p.run_queries(g,queries,out,solver,deadline)
        names={1:'SAT',0:'UNKNOWN',-1:'UNSAT'}
        for i,c in enumerate(candidates):
            triple=ans[3*i:3*i+3];require(triple[0]!=-1,'SAT query contradicts full replay')
            c['diagnostic_proof']=dict(zip(('free','reset','image'),map(names.get,triple)))
            c['qualified_offline_opportunity']=triple==[1,-1,-1]
            c['receipts']={phase:dict(cnf_sha256=report['cnf_sha256'],queries_sha256=report['queries_sha256'],
                results_sha256=report['results_sha256'],solver_sha256=solver_hash,row=3*i+j,
                assumptions=queries[3*i+j],result=names[triple[j]]) for j,phase in enumerate(('free','reset','image'))}
    else: report=dict(queries=0,conflicts_per_query=1000,status='NO_NEW_RETAINED_IDENTITIES')
    write(out/'candidates.json',candidates);write(out/'report.json',report)
    return report

def case(p,d,ordinary,source,name,out,solver,protocol):
    out.mkdir();deadline=p.Deadline(protocol['case_seconds']);start=deadline.start
    origin=ordinary/name;source=source/name;job=read(origin/'job.json');cfg=p.Config(**job['config'])
    require(cfg.lanes==256 and cfg.candidates_per_root==8 and job['chunk_roots']==32,'frozen lane/top-k/chunk changed')
    roots=[json.loads(x) for x in (origin/'root_search.jsonl').read_text().splitlines()][:32]
    require(len(roots)==32 and read(source/'result.json')['status']=='COMPLETE','incomplete frozen source')
    old=read(origin/'chunks/chunk_00000/candidates.json');inputpath=Path(job['case']['input'])
    require(sha(inputpath)==job['case']['input_sha256'],'input mismatch')
    a=p.Aiger(inputpath);ia=IndependentAig(inputpath);g,base,step,reset=p.compile_graph(a)
    bound=d.verify_source(p,ordinary,origin,job,old,g,dict(free=base,reset=reset,step=step),out,solver)
    (initial_free,image,resetvalues),initial_mask=p.signatures(g,[base,step,reset],cfg)
    seq=[x|(y<<cfg.lanes) for x,y in zip(image,resetvalues)];seqmask=(1<<(2*cfg.lanes))-1
    models,samples=verify_saved_models(d,p,a,g,base,step,old,source,out,deadline,ia)
    qualified=verify_saved_proofs(p,a,g,[('free',base),('reset',reset),('image',step)],old,source,out,initial_free,ia)
    seq,seqmask=d.append_samples(seq,seqmask,samples)
    initial=worlds(initial_free,a.ni,a.nl,cfg.lanes)
    # Recompute every world on the original AIG, rather than splicing signatures.
    for lane,w in enumerate(initial):
        values=a.step(w['inputs'],w['state'])[2]
        require(values==[(v>>lane)&1 for v in initial_free],'initial free source mismatch')
        require(ia.values(w['inputs'],w['state'])==values,'independent initial full-world mismatch')
    b=choose_models(models,initial,'previous_inputs');c=choose_models(models,initial,'current_inputs')
    randoms=random_worlds(a.ni,a.nl,max(len(b),len(c)),protocol['random_seed'],initial)
    extras=dict(A=[],B=b,C=c,random_B=randoms[:len(b)],random_C=randoms[:len(c)])
    free_by_arm={};masks={};armplan={}
    known={tuple(w['state']) for w in worlds(image,a.ni,a.nl,cfg.lanes)}|{tuple(m['successor_state']) for m in models}
    for arm,extra in extras.items():
        free,mask=append_worlds(a,initial_free,initial_mask,extra);free_by_arm[arm]=free;masks[arm]=mask
        for offset,w in enumerate(extra,cfg.lanes):
            require(ia.values(w['inputs'],w['state'])==[(v>>offset)&1 for v in free],'independent appended full-world mismatch')
        armplan[arm]=dict(added=len(extra),free_domain_sha256=digest(dict(free=free,mask=mask)),
                          extra_worlds=extra,diagnostics=domain_diagnostics(extra,known,list(a.initial)))
    files=[inputpath,origin/'job.json',origin/'root_search.jsonl',origin/'chunks/chunk_00000/candidates.json']
    files+=sorted(f for f in source.rglob('*') if f.is_file())
    bound.update({f:sha(f) for f in files})
    freeze=dict(case=name,input=str(inputpath),input_sha256=sha(inputpath),config=job['config'],roots=roots,
                sequence_signatures=seq,sequence_mask=seqmask,sequence_sha256=digest(dict(seq=seq,mask=seqmask)),
                initial_free_signatures=initial_free,initial_free_mask=initial_mask,initial_worlds=initial,
                source_model_order_sha256=digest(models),source_model_count=len(models),arms=armplan,
                known_image_state_count=len(known),initial_diagnostics=domain_diagnostics(initial,known,list(a.initial)),
                source_hashes={str(k):v for k,v in bound.items()})
    write(out/'frozen_inputs.json',freeze);frozenhash=sha(out/'frozen_inputs.json');prep=time.monotonic()-start
    results={};reuse={};candidates_by_arm={};new={};traces=[];initial_ids=None
    for arm in extras:
        deadline.remaining();free=free_by_arm[arm];mask=masks[arm];domain=armplan[arm]['free_domain_sha256'];t=time.monotonic()
        if domain in reuse:
            previous=reuse[domain];found=copy.deepcopy(candidates_by_arm[previous]);stats=results[previous]['stats'];reused=previous
        else:
            found,stats=d.search_same_pool(p,p.Structure(a),roots,seq,seqmask,free,mask,cfg,deadline,out/(arm+'_roots.jsonl'))
            reuse[domain]=arm;reused=None
        require(digest(dict(seq=seq,mask=seqmask))==freeze['sequence_sha256'],'sequence domain mutated')
        ids={cid(x) for x in found}
        if arm=='A':
            expected=read(source/'refined_candidates.json')
            require(len(found)==len(expected) and all(all(c[k]==e.get(k) for k in c) for c,e in zip(found,expected)), 'A initial-arm identity/metadata differs from saved first refinement')
            require(stats==read(source/'result.json')['refined']['stats'],'A search funnel differs')
            initial_ids=ids
        for cand in found:
            cand['free_witness']=p.witness(a,cand,free);independent_witness(ia,cand,cand['free_witness'],free)
            if cid(cand) not in initial_ids:
                initialdiff=p.recipe_eval(cand['recipe'],cand['out'],initial_free,initial_mask)^initial_free[cand['root']]
                require(initialdiff==0 and cand['witness_lane']>=cfg.lanes,'new retained identity was not an initial free-filter rejection')
                require(p.recipe_eval(cand['recipe'],cand['out'],seq,seqmask)==seq[cand['root']],'changed sequence predicate')
                trace=dict(arm=arm,candidate_id=list(cid(cand)),initial_free_difference=initialdiff,
                           initial_rejection='no_sampled_free_witness',witness_lane=cand['witness_lane'],
                           sequence_equal=True,conservative_gain=cand['conservative_gain'],
                           nonlinear_divisor=any(n>a.ni+a.nl for n in cand['divisors']),
                           justification='The frozen enumeration/normalization sees the identical sequence domain and ordered pool. This exact normalized identity has zero original-free difference, so the unmodified accept predicate rejects it before cost/nonlinearity/top-k.')
                traces.append(trace)
                if cid(cand) not in new:
                    new[cid(cand)]=copy.deepcopy(cand);new[cid(cand)]['first_discovery_arm']=arm
            elif arm!='A':
                baseline=next(x for x in candidates_by_arm['A'] if cid(x)==cid(cand))
                require(cand['witness_lane']==baseline['witness_lane'],'original witness lane changed')
        candidates_by_arm[arm]=found;write(out/(arm+'_candidates.json'),found)
        results[arm]=dict(added_worlds=len(extras[arm]),candidates=len(found),new_retained=len(ids-initial_ids),
                          retained_A=len(ids&initial_ids),known_qualified=sum(qualified.get(cid(x),False) for x in found),
                          stats=stats,search_wall_s=time.monotonic()-t,reused_identical_domain_from=reused,
                          free_domain_sha256=domain)
    proofstart=time.monotonic();proof=proof_new(p,a,ia,list(new.values()),free_by_arm,solver,out/'new_proofs',deadline)
    for arm in extras:
        ids={cid(c) for c in candidates_by_arm[arm]}
        results[arm]['new_qualified']=sum(c['qualified_offline_opportunity'] for ident,c in new.items() if ident in ids)
    write(out/'new_identity_filter_traces.json',traces)
    require(sha(out/'frozen_inputs.json')==frozenhash,'case freeze changed')
    for path,value in bound.items(): require(sha(path)==value,'source/tool changed during diagnostic')
    deadline.remaining()
    result=dict(case=name,status='COMPLETE',case_cap_s=protocol['case_seconds'],elapsed_s=time.monotonic()-start,
                preparation_wall_s=prep,proof_and_final_checks_wall_s=time.monotonic()-proofstart,arms=results,
                new_identity_union=len(new),new_qualified_union=sum(x['qualified_offline_opportunity'] for x in new.values()),
                proof=proof,independent_full_world_and_witness_replay='PASS',initial_arm_exact_identity='PASS',
                source_integrity='PASS',frozen_inputs_sha256=frozenhash,sequence_domain_identical=True,
                area_measured=False,main_transform_budget_claim=False,native_novelty='NOT_CHECKED')
    write(out/'result.json',result);return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--ordinary',type=Path,required=True);ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--solver',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    require(not args.out.exists(),'new output directory required');args.out.mkdir(parents=True)
    protocol=read(HERE/'protocol.json');manifest=read(args.source/'source_manifest.json')
    for name,expected in manifest.items(): require(sha(args.source/'source'/name)==expected,'source diagnostic changed')
    spec=importlib.util.spec_from_file_location('frozen_image_diagnostic',args.source/'source/diagnostic.py')
    d=importlib.util.module_from_spec(spec);spec.loader.exec_module(d);p=d.load_runtime(args.ordinary/'source')
    ordinaryplan=read(args.ordinary/'plan.json');require(sha(args.solver)==ordinaryplan['solver_sha256'],'wrong frozen ordinary solver')
    code={str(f):sha(f) for f in sorted(HERE.glob('*.py'))};code[str(HERE/'protocol.json')]=sha(HERE/'protocol.json')
    plan=dict(protocol=protocol,source=str(args.source.resolve()),ordinary=str(args.ordinary.resolve()),
              solver=str(args.solver.resolve()),solver_sha256=sha(args.solver),tool_sources=code,
              runtime_sources=ordinaryplan['runtime_source_hashes'],source_diagnostic_manifest=manifest,
              python=sys.version,workers=1,timing_note='Preparation, arms, proof, and in-case independent replay all count toward 120s/case; products/DSEC, if justified, are a separate experiment.')
    write(args.out/'plan.json',plan);frozen=args.out/'source';frozen.mkdir()
    for path in code: shutil.copy2(path,frozen/Path(path).name)
    rows=[]
    for name in protocol['cases']:
        t=time.monotonic()
        try: row=case(p,d,args.ordinary,args.source,name,args.out/name,args.solver.resolve(),protocol)
        except Exception as e:
            import traceback
            row=dict(case=name,status='TIMEOUT' if isinstance(e,(TimeoutError,subprocess.TimeoutExpired)) else 'ERROR',error=repr(e),elapsed_s=time.monotonic()-t)
            (args.out/name/'traceback.txt').write_text(traceback.format_exc());write(args.out/name/'result.json',row)
        rows.append(row);write(args.out/'results.json',rows);print(json.dumps(row),flush=True)
    for path,h in code.items(): require(sha(path)==h,'diagnostic code changed during experiment')
    write(args.out/'source_integrity.json',dict(status='PASS',hashes=code))
if __name__=='__main__': main()
