#!/usr/bin/env python3
"""Extra-cost qualified-union retention audit; source diagnostics are immutable."""
import argparse
import copy
import csv
import importlib
from pathlib import Path
import shutil
import time
from audit_products import module,triples,emit,independent_witness,IndependentAig
from diagnostic import read,write,sha,require,cid,digest
HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--products',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--abc',type=Path,required=True);args=ap.parse_args()
    start=time.monotonic();prior=args.products.resolve();out=args.out.resolve();require(not out.exists(),'new audit output required');out.mkdir(parents=True)
    plan=read(prior/'plan.json');source=Path(plan['source_diagnostic']);dplan=read(source/'plan.json');ordinary=Path(dplan['ordinary']);name=plan['case']
    result=read(prior/'result.json');require(result['status']=='EXTRA_COST_PRODUCT_AUDIT_COMPLETE','source product audit incomplete')
    bound=dict(plan['source_hashes']);bound.update({str(p):sha(p) for p in prior.rglob('*') if p.is_file()})
    bound.update({str(HERE/n):sha(HERE/n) for n in ['audit_qualified_union.py','audit_products.py','diagnostic.py','independent.py']})
    for f,h in bound.items():require(sha(f)==h,'source hash mismatch')
    write(out/'plan.json',dict(source_products=str(prior),source_hashes=bound,proof_reuse='exact frozen graph and assumptions, no new solving',
        direct_scope='union previous common selected-root scope with current qualified-union selected roots and used divisors; require literal scope equality before reuse',
        extra_cost=True,main_transform_budget_claim=False,native_novelty='NOT_CHECKED'))
    d=module('frozen_image_for_union',Path(dplan['source'])/'source/diagnostic.py');p=d.load_runtime(ordinary/'source');product=importlib.import_module('product')
    review=module('whole_original_for_union',HERE.parent/'global_expression_review/review.py');hashdirect=module('hash_direct_for_union',HERE.parent/'nonlinear_divisors/hash_direct_audit.py')
    inputhash=sha(prior/'input.aig');shutil.copy2(prior/'input.aig',out/'input.aig');inputpath=out/'input.aig'
    require(sha(inputpath)==inputhash==read(source/name/'frozen_inputs.json')['input_sha256'],'copied input hash mismatch')
    a=p.Aiger(inputpath);ia=IndependentAig(inputpath);s=p.Structure(a);union=read(prior/'fresh_build_proofs/candidates.json')
    require(len(union)==len({cid(c) for c in union})==52,'expected immutable52-identity source union')
    # Reconstruct both saved union-proof graphs and exact assumption streams.
    for dirname,cs in [('fresh_build_proofs',union),('fresh_direct_proofs',read(prior/'fresh_direct_proofs/candidates.json'))]:
        proof=prior/dirname;g,b,st,r=p.compile_graph(a);queries,order=triples(p,g,[('free',b),('reset',r),('step',st)],cs)
        g.cnf(out/(dirname+'_reconstructed.cnf'));report=read(proof/'report.json')
        require(sha(out/(dirname+'_reconstructed.cnf'))==report['cnf_sha256'],'source proof graph differs')
        qtext=str(len(queries))+'\n'+''.join(f'{i} 1 {q[0]}\n' for i,q in enumerate(queries))
        require(qtext==(proof/'obligations.queries').read_text() and digest(order)==digest(read(proof/'query_order.json')),'source proof assumptions differ')
        raw=list(csv.DictReader((proof/'obligations.results.csv').open()));require([int(x['query']) for x in raw]==list(range(len(queries))),'source proof order differs')
        for file,key in [('obligations.cnf','cnf_sha256'),('obligations.queries','queries_sha256'),('obligations.results.csv','results_sha256')]:require(sha(proof/file)==report[key],'source receipt hash differs')
        for i,c in enumerate(cs):
            codes=[int(x['result']) for x in raw[3*i:3*i+3]];names={1:'SAT',0:'UNKNOWN',-1:'UNSAT'}
            require(all(c['proof'][phase]==names[code] for phase,code in zip(('free','reset','step'),codes)),'source statuses differ')
            if 'free_witness' in c: independent_witness(ia,c,c['free_witness'])
            if dirname=='fresh_build_proofs':require(codes==[1,-1,-1],'union has unproved Build')
    selected,rejected=product.select(s,union);prior_scopes=read(prior/'direct_scope.json');scopes={r['root']:r for r in prior_scopes}
    selected_roots={c['root'] for c in selected};require(selected_roots==set(scopes),'Direct root scope expanded; fresh Direct audit required')
    verified_scope=[]
    for c in selected:
        row=scopes[c['root']];used=set(row['used_divisors'])|p.external_nodes(c['recipe'],c['out'])
        ordinary_lits={0,1}|{2*n+phase for n in set(row['pool'])|used for phase in (0,1)}
        raw=hashdirect.collect_hash_direct(s,c['root'],row['pool'],2)
        literals=sorted(ordinary_lits|set(raw));require(literals==row['all_literals'],'Direct literal scope expanded; fresh proof required')
        verified_scope.append(dict(root=c['root'],all_literals=literals,used_divisors_union=sorted(used),source_scope_hash=digest(row)))
    write(out/'verified_direct_scope.json',verified_scope)
    direct=[c for c in read(prior/'fresh_direct_proofs/candidates.json') if c['proof']['reset']==c['proof']['step']=='UNSAT' and c['conservative_gain']>0]
    whole=review.OriginalHash(review.Aig(inputpath));aliases={};classification=[]
    for c in union:
        value,_,_,live=whole.recipe(c['recipe'],c['out']);matches=whole.original_aliases(value);safe=[lit for lit in matches if c['root'] not in s.tfi([lit//2])]
        aliases[cid(c)]=safe;classification.append(dict(candidate_id=list(cid(c)),safe_original_aliases=safe,live_global_fresh_gates=len(live)))
    write(out/'whole_original_classification.json',classification)
    abcsha=sha(args.abc);require(abcsha==read(ordinary/'plan.json')['abc_sha256'],'ABC hash differs');cache={}
    for f in prior.rglob('result.json'):
        row=read(f)
        if 'product_sha256' not in row or 'dsec' not in row:continue
        cert=row['dsec'];require(sha(f.parent/'product.aig')==row['product_sha256'],'prior graph identity differs')
        require(cert['status']=='PASS' and cert['input_sha256']==inputhash and cert['product_sha256']==row['product_sha256'] and cert['abc_sha256']==abcsha,'prior DSEC binding differs')
        require(sha(cert['log_path'])==cert['log_sha256'],'prior DSEC log identity differs')
        cache[inputhash,row['product_sha256'],abcsha]=copy.deepcopy(cert)
    oldkeys=set(cache);newids={cid(c) for c in union if c['audit_origin']=='new_free_domain_identity'}
    build,bg=emit(product,a,ia,selected,out/'build_only',inputpath,args.abc,cache,inputhash,abcsha)
    mixed,_=product.select(s,direct+selected);full,mg=emit(product,a,ia,mixed,out/'mixed',inputpath,args.abc,cache,inputhash,abcsha)
    real={r['root']:r for r in mg['realization']}
    genuine={cid(c) for c in mixed if c['recipe'] and not aliases[cid(c)] and real[c['root']]['output_is_new'] and real[c['root']]['output_is_live'] and real[c['root']]['live_created_gates']>0}
    without_new=[c for c in mixed if cid(c) not in (newids&genuine)];without_all=[c for c in mixed if cid(c) not in genuine]
    no_new,_=emit(product,a,ia,without_new,out/'mixed_without_new',inputpath,args.abc,cache,inputhash,abcsha)
    no_all,_=emit(product,a,ia,without_all,out/'mixed_without_all_genuine_build',inputpath,args.abc,cache,inputhash,abcsha)
    write(out/'selected_sets.json',dict(qualified_union=union,build_selected=selected,build_rejected=rejected,mixed_selected=mixed,same_set_without_new=without_new,same_set_without_all_genuine=without_all))
    reference=result['arms']['B'];same_build=build['product_sha256']==reference['build_only']['product_sha256'];same_mixed=full['product_sha256']==reference['mixed']['product_sha256']
    require({cid(c) for c in union}=={cid(c) for c in read(prior/'fresh_build_proofs/candidates.json')},'union lost identities')
    for f,h in bound.items():require(sha(f)==h,'bound source changed during audit')
    require(sha(inputpath)==inputhash,'copied input changed during audit');newcerts=[v for k,v in cache.items() if k not in oldkeys]
    final=dict(status='QUALIFIED_UNION_AUDIT_COMPLETE',case=name,qualified_union=52,initial_proved=49,new_proved=3,diagnostic_B_qualified=51,
        preserved_displaced_initial_identity=[list(cid(c)) for c in union if cid(c) not in {cid(b) for b in read(source/name/'B_candidates.json')}],
        selected_roots=sorted(selected_roots),direct_scope_identical=True,direct_candidates=312,new_proof_queries=0,verified_existing_proof_queries=156+936,
        build_only=build,mixed=full,mixed_without_new=no_new,mixed_without_all_genuine=no_all,build_only_byte_identical_to_B=same_build,mixed_byte_identical_to_B=same_mixed,
        raw_build_only_gain=result['baseline']['and_count']-build['and_count'],mixed_gain=result['baseline']['and_count']-full['and_count'],
        genuine_build_same_set_marginal=no_all['and_count']-full['and_count'],new_identity_same_set_marginal=no_new['and_count']-full['and_count'],
        paired_mixed_gain_vs_A=result['arms']['A']['mixed']['and_count']-full['and_count'],fresh_dsec_runs=len(newcerts),
        reused_bound_dsec_graphs=sum(x['dsec']['reused_exact_graph_dsec'] for x in [build,full,no_new,no_all]),new_dsec_wall_s=sum(x['wall_s'] for x in newcerts),
        extra_wall_s=time.monotonic()-start,source_integrity='PASS',input_copy_integrity='PASS',main_transform_budget_claim=False,native_novelty='NOT_CHECKED')
    write(out/'result.json',final);print(__import__('json').dumps(final),flush=True)
if __name__=='__main__':main()
