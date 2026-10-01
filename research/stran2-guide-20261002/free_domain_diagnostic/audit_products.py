#!/usr/bin/env python3
"""Extra-cost exact products for the frozen free-domain diagnostic.

No online integration. Uses the frozen product runtime and independent complete
original structural hashing. Direct scope is shared across A/B/C selected roots.
"""
from __future__ import annotations
import argparse
import copy
import csv
import importlib
import importlib.util
import json
from pathlib import Path
import random
import shutil
import sys
import time
from diagnostic import read,write,sha,require,cid,digest,clone_graph
from independent import Aig as IndependentAig, recipe as independent_recipe, witness as independent_witness
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def triples(p,g,maps,candidates):
    queries=[];order=[]
    for i,c in enumerate(candidates):
        for phase,mapping in maps:
            lit=g.xor(mapping[c['root']],p.graph_recipe(g,mapping,c['recipe'],c['out']))
            order.append(dict(query=len(queries),candidate_index=i,candidate_id=list(cid(c)),phase=phase,assumptions=[lit]))
            queries.append([lit])
    return queries,order

def check_new_receipts(p,a,source,out):
    cs=read(source/'new_proofs/candidates.json');g,b,s,r=p.compile_graph(a)
    qs,order=triples(p,g,[('free',b),('reset',r),('image',s)],cs)
    g.cnf(out/'new_proof_reconstructed.cnf');report=read(source/'new_proofs/report.json')
    require(sha(out/'new_proof_reconstructed.cnf')==report['cnf_sha256'],'new diagnostic CNF mismatch')
    text=str(len(qs))+'\n'+''.join(f'{i} 1 {q[0]}\n' for i,q in enumerate(qs))
    require(text==(source/'new_proofs/obligations.queries').read_text(),'new diagnostic assumptions mismatch')
    raw=list(csv.DictReader((source/'new_proofs/obligations.results.csv').open()))
    require([int(x['query']) for x in raw]==list(range(len(qs))),'new receipt ordering')
    for file,key in [('obligations.cnf','cnf_sha256'),('obligations.queries','queries_sha256'),('obligations.results.csv','results_sha256')]:
        require(sha(source/'new_proofs'/file)==report[key],'new receipt hash mismatch')
    names={1:'SAT',0:'UNKNOWN',-1:'UNSAT'}
    for i,c in enumerate(cs):
        codes=[int(x['result']) for x in raw[3*i:3*i+3]]
        require(c['diagnostic_proof']==dict(zip(('free','reset','image'),map(names.get,codes))),'new diagnostic status mismatch')
        require(c['qualified_offline_opportunity']==(codes==[1,-1,-1]),'new diagnostic qualification mismatch')
    return cs

def prove(p,a,ia,candidates,solver,out,build):
    out.mkdir();g,b,s,r=p.compile_graph(a);qs,order=triples(p,g,[('free',b),('reset',r),('step',s)],candidates)
    ans,report=p.run_queries(g,qs,out,solver,p.Deadline(120));write(out/'query_order.json',order)
    names={1:'SAT',0:'UNKNOWN',-1:'UNSAT'};valid=[];solverhash=sha(solver)
    for i,c in enumerate(candidates):
        triple=ans[3*i:3*i+3]
        if 'free_witness' in c:
            independent_witness(ia,c,c['free_witness'])
            vals=a.step(c['free_witness']['inputs'],c['free_witness']['state'])[2]
            require(vals[c['root']]!=p.recipe_eval(c['recipe'],c['out'],vals),'full witness replay fails')
            require(triple[0]!=-1,'free proof contradicts witness')
        c['proof']=dict(zip(('free','reset','step'),map(names.get,triple)))
        c['proof']['free_witness_replayed']='free_witness' in c
        c['receipts']={phase:dict(cnf_sha256=report['cnf_sha256'],queries_sha256=report['queries_sha256'],results_sha256=report['results_sha256'],
            assumptions=qs[3*i+j],row=3*i+j,result=names[triple[j]],solver_sha256=solverhash) for j,phase in enumerate(('free','reset','step'))}
        c['qualified_offline_opportunity']=triple==[1,-1,-1]
        if build:
            require(triple==[1,-1,-1],'fresh check failed previously proved Build');valid.append(c)
        elif triple[1:]==[-1,-1] and c['conservative_gain']>0:
            valid.append(c)
    write(out/'candidates.json',candidates);write(out/'report.json',report);return valid,report

def independent_product(ia,chosen,path):
    pa=IndependentAig(path);rng=random.Random(2026100214);replace={c['root']:c for c in chosen}
    require((ia.ni,ia.nl,ia.no)==(pa.ni,pa.nl,pa.no),'product interface differs')
    for _ in range(128):
        inputs=[rng.randrange(2) for _ in range(ia.ni)];state=[rng.randrange(2) for _ in range(ia.nl)]
        values=[0]+inputs+state
        for node,(x,y) in enumerate(ia.gates,ia.ni+ia.nl+1):
            if node in replace:
                c=replace[node];v=independent_recipe(c['recipe'],c['out'],values)
            else:v=(values[x//2]^(x&1))&(values[y//2]^(y&1))
            values.append(v)
        expected=[values[x//2]^(x&1) for x in ia.outputs+ia.latches]
        actual=pa.values(inputs,state);observed=[actual[x//2]^(x&1) for x in pa.outputs+pa.latches]
        require(expected==observed,'independent product CO replay differs from substitutions')
    return dict(status='PASS',random_free_assignments=128,all_PO_RI=True,comparison='independently evaluated original graph with exact selected substitutions versus decoded product; not original/product free equivalence')

def emit(product,a,ia,selected,path,inputpath,abc,cache,inputhash,abchash):
    path.mkdir();g=product.rebuild(a,selected);h=product.write_aig(path/'product.aig',g)
    write(path/'selection.json',dict(selected=selected,realization=g['realization']))
    replay=independent_product(ia,selected,path/'product.aig');key=(inputhash,h,abchash)
    if key in cache:
        cert=copy.deepcopy(cache[key]);cert.update(reused_exact_graph_dsec=True,charged_new_wall_s=0.0)
    else:
        cert=product.dsec(abc,inputpath,path/'product.aig',path,120,'dsec')
        cert.update(reused_exact_graph_dsec=False,charged_new_wall_s=cert['wall_s'],log_path=str((path/'dsec.log').resolve()),input_sha256=inputhash,product_sha256=h,abc_sha256=abchash)
        require(cert['status']=='PASS','DSEC did not pass');cache[key]=copy.deepcopy(cert)
    require(sha(cert['log_path'])==cert['log_sha256'],'DSEC log binding differs')
    result=dict(and_count=len(g['gates']),product_sha256=h,selected=len(selected),dsec=cert,independent_product_replay=replay)
    write(path/'result.json',result);return result,g

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--diagnostic',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--solver',type=Path,required=True);ap.add_argument('--abc',type=Path,required=True);args=ap.parse_args()
    start=time.monotonic();require(not args.out.exists(),'new product audit output required');args.out.mkdir(parents=True)
    plan=read(args.diagnostic/'plan.json');ordinary=Path(plan['ordinary']);originaldiag=Path(plan['source']);name='045_mem_ctrl'
    source=args.diagnostic/name;freeze=read(source/'frozen_inputs.json');job=read(ordinary/name/'job.json');cfg_data=job['config']
    require(read(source/'result.json')['new_qualified_union']>0,'no new proved identities: no product audit justified')
    require(read(args.diagnostic/'source_integrity.json')['status']=='PASS','diagnostic integrity missing')
    bound={str(f.resolve()):sha(f) for f in args.diagnostic.rglob('*') if f.is_file()}
    bound.update(freeze['source_hashes']);bound[str(Path(__file__).resolve())]=sha(__file__)
    bound[str(HERE/'diagnostic.py')]=sha(HERE/'diagnostic.py');bound[str(HERE/'independent.py')]=sha(HERE/'independent.py')
    d=module('frozen_image_source',originaldiag/'source/diagnostic.py');p=d.load_runtime(ordinary/'source');product=importlib.import_module('product')
    review=module('independent_original_hash',PACKAGE/'global_expression_review/review.py')
    hashdirect=module('bounded_hash_direct',PACKAGE/'nonlinear_divisors/hash_direct_audit.py')
    bound.update({str(Path(m.__file__).resolve()):sha(m.__file__) for m in (p,product,review,hashdirect)})
    bound[str(args.solver.resolve())]=plan['solver_sha256'];bound[str(args.abc.resolve())]=read(ordinary/'plan.json')['abc_sha256']
    for file,h in bound.items():require(sha(file)==h,'bound source/input/tool changed')
    write(args.out/'plan.json',dict(case=name,source_diagnostic=str(args.diagnostic.resolve()),source_hashes=bound,
        arms=['A','B','C','random_B','random_C'],direct_scope='shared union of selected roots, constants, both phases of original pools and all selected used divisors, plus frozen 1/2-AND grammar zero-fresh outputs',
        extra_cost=True,main_transform_budget_claim=False,native_novelty='NOT_CHECKED'))
    inputpath=Path(freeze['input']);shutil.copy2(inputpath,args.out/'input.aig');inputpath=args.out/'input.aig'
    a=p.Aiger(inputpath);ia=IndependentAig(inputpath);s=p.Structure(a);cfg=p.Config(**cfg_data)
    new=check_new_receipts(p,a,source,args.out);newids={cid(c) for c in new if c['qualified_offline_opportunity']}
    oldproof=read(originaldiag/name/'new_proofs/candidates.json')+read(ordinary/name/'chunks/chunk_00000/candidates.json')
    qualification={cid(c):c['qualified_offline_opportunity'] for c in oldproof+new}
    arms={};union={}
    for arm in plan['protocol']['arms']:
        cs=[copy.deepcopy(c) for c in read(source/(arm+'_candidates.json')) if qualification[cid(c)]]
        for c in cs:
            c['audit_origin']='new_free_domain_identity' if cid(c) in newids else 'initial_A_identity'
            cost=s.cost(c['root'],c['recipe'],c['out']);require(all(c[k]==v for k,v in cost.items()),'stale recipe cost')
            require(p.normalize(s,c['root'],c['recipe'],c['out'])==(c['recipe'],c['out']),'not normalized')
            independent_witness(ia,c,c['free_witness']);union.setdefault(cid(c),c)
        arms[arm]=cs
    valid,buildproof=prove(p,a,ia,list(union.values()),args.solver.resolve(),args.out/'fresh_build_proofs',True)
    verified={cid(c):c for c in valid};arms={k:[verified[cid(c)] for c in cs] for k,cs in arms.items()}
    # Independent all-original canonical classification, not just prefix hash.
    originalhash=review.OriginalHash(review.Aig(inputpath));classifications={};records=[]
    for c in valid:
        value,built,fresh,live=originalhash.recipe(c['recipe'],c['out']);aliases=originalhash.original_aliases(value)
        safe=[lit for lit in aliases if c['root'] not in s.tfi([lit//2])]
        require(not aliases or safe,'only cyclic original output aliases')
        row=dict(candidate_id=list(cid(c)),original_output_aliases=aliases,safe_original_aliases=safe,live_global_fresh_gates=len(live))
        classifications[cid(c)]=row;records.append(row)
    write(args.out/'whole_original_classification.json',records)
    selections={k:product.select(s,cs)[0] for k,cs in arms.items()}
    selected_union={cid(c):c for cs in selections.values() for c in cs};pools={row['root']:row['pool'] for row in freeze['roots']}
    byroot={}
    for c in selected_union.values():byroot.setdefault(c['root'],[]).append(c)
    directs=[];scope=[];initialfree=freeze['initial_free_signatures'];fm=freeze['initial_free_mask']
    for root,cs in sorted(byroot.items()):
        used=set().union(*(p.external_nodes(c['recipe'],c['out']) for c in cs))
        ordinarylits={0,1}|{2*n+phase for n in set(pools[root])|used for phase in (0,1)}
        raw=hashdirect.collect_hash_direct(s,root,pools[root],cfg.max_gates)
        for value,witness in raw.items():require(p.normalize(s,root,witness['recipe'],witness['out'])==([],value),'Direct grammar witness mismatch')
        lits=sorted(ordinarylits|set(raw));scope.append(dict(root=root,pool=pools[root],used_divisors=sorted(used),all_literals=lits,
            extra_hash_literals=sorted(set(raw)-ordinarylits),raw_grammar_witnesses=raw))
        for lit in lits:
            c=dict(root=root,recipe=[],out=lit,**s.cost(root,[],lit),audit_origin='bounded_direct')
            diff=initialfree[root]^p.recipe_eval([],lit,initialfree,fm)
            if diff:c['witness_lane']=(diff&-diff).bit_length()-1;c['free_witness']=p.witness(a,c,initialfree)
            directs.append(c)
    write(args.out/'direct_scope.json',scope)
    directvalid,directproof=prove(p,a,ia,directs,args.solver.resolve(),args.out/'fresh_direct_proofs',False)
    inputhash=sha(inputpath);abchash=sha(args.abc);cache={};baseline,_=emit(product,a,ia,[],args.out/'baseline',inputpath,args.abc,cache,inputhash,abchash)
    dselected,_=product.select(s,directvalid);directonly,_=emit(product,a,ia,dselected,args.out/'direct_only',inputpath,args.abc,cache,inputhash,abchash)
    results={};cached_arm_sets={}
    for arm,candidates in arms.items():
        path=args.out/arm;path.mkdir();ident=digest([list(cid(c)) for c in candidates])
        if ident in cached_arm_sets:
            old=cached_arm_sets[ident];result=copy.deepcopy(results[old]);result.update(reused_identical_candidate_set_from=old)
            write(path/'result.json',result);results[arm]=result;continue
        chosen=selections[arm];full,rebuilt=emit(product,a,ia,chosen,path/'build_only',inputpath,args.abc,cache,inputhash,abchash)
        nonew=[c for c in chosen if cid(c) not in newids]
        withoutnew,_=emit(product,a,ia,nonew,path/'build_only_without_new',inputpath,args.abc,cache,inputhash,abchash)
        # Attribute the arm's actual Build-only selection against the common bounded Direct set.
        mixed,_=product.select(s,directvalid+chosen)
        mixedfull,mixedgraph=emit(product,a,ia,mixed,path/'mixed',inputpath,args.abc,cache,inputhash,abchash)
        real={r['root']:r for r in mixedgraph['realization']}
        genuine=[c for c in mixed if c['recipe'] and real[c['root']]['output_is_new'] and real[c['root']]['output_is_live'] and
                 real[c['root']]['live_created_gates']>0 and not classifications[cid(c)]['safe_original_aliases']]
        genuineids={cid(c) for c in genuine}
        removeall=[c for c in mixed if cid(c) not in genuineids]
        noall,_=emit(product,a,ia,removeall,path/'mixed_without_genuine_build',inputpath,args.abc,cache,inputhash,abchash)
        newgenuine=newids&genuineids;removenew=[c for c in mixed if cid(c) not in newgenuine]
        mixednonew,_=emit(product,a,ia,removenew,path/'mixed_without_new_genuine_build',inputpath,args.abc,cache,inputhash,abchash)
        write(path/'selected_sets.json',dict(build_only=chosen,mixed=mixed,genuine_build=genuine,new_genuine_ids=[list(x) for x in sorted(newgenuine)],
            same_mixed_without_all_genuine=removeall,same_mixed_without_new_genuine=removenew))
        result=dict(qualified_candidates=len(candidates),build_only=full,build_only_without_new=withoutnew,
            raw_build_only_gain=baseline['and_count']-full['and_count'],new_identity_same_build_selected_set_marginal=withoutnew['and_count']-full['and_count'],
            mixed=mixedfull,mixed_without_genuine_build=noall,mixed_without_new_genuine_build=mixednonew,
            exact_mixed_gain=baseline['and_count']-mixedfull['and_count'],genuine_builds=len(genuine),new_genuine_builds=len(newgenuine),
            full_genuine_build_same_mixed_set_marginal=noall['and_count']-mixedfull['and_count'],
            new_genuine_build_same_mixed_set_marginal=mixednonew['and_count']-mixedfull['and_count'],
            reused_identical_candidate_set_from=None)
        results[arm]=result;cached_arm_sets[ident]=arm;write(path/'result.json',result)
    for arm,result in results.items():
        result['build_only_gain_difference_vs_A']=result['raw_build_only_gain']-results['A']['raw_build_only_gain']
        result['genuine_build_marginal_difference_vs_A']=result['full_genuine_build_same_mixed_set_marginal']-results['A']['full_genuine_build_same_mixed_set_marginal']
        result['mixed_product_gain_difference_vs_A']=result['exact_mixed_gain']-results['A']['exact_mixed_gain']
        write(args.out/arm/'result.json',result)
    for file,h in bound.items():require(sha(file)==h,'source evidence/tool changed during product audit')
    total=time.monotonic()-start;dsecs=list(cache.values());dsecwall=sum(x['wall_s'] for x in dsecs)
    result=dict(case=name,status='EXTRA_COST_PRODUCT_AUDIT_COMPLETE',arms=results,baseline=baseline,direct_only=directonly,
        direct_candidates=len(directs),proved_positive_directs=len(directvalid),direct_roots=len(byroot),
        grammar_hash_extra_literals=sum(len(x['extra_hash_literals']) for x in scope),build_proof=buildproof,direct_proof=directproof,
        whole_original_classified=len(valid),new_identity_original_output_aliases=sum(bool(classifications[x]['safe_original_aliases']) for x in newids),
        loaded_and=job['case']['loaded_AND'],input_and=a.na,extra_wall_s=total,extra_non_dsec_wall_s=total-dsecwall,
        fresh_dsec_runs=len(cache),fresh_dsec_wall_s=dsecwall,all_dsec='PASS',source_integrity='PASS',
        same_original_120s_budget=False,global_boolean_direct_exhaustion=False,native_novelty='NOT_CHECKED',
        scope='Only mem_ctrl fixed first32 post-first-image-refinement search; fresh proof and extra-cost exact products; no online/full55 conclusion')
    write(args.out/'result.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__': main()
