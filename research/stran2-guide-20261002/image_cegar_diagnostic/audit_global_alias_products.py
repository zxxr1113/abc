#!/usr/bin/env python3
"""Whole-original structural aliases and exact selected-set Build demotion.

Original recipe materialization is retained. A later original ID is not treated
as fresh merely because the stable replay constructs that expression earlier.
Only aliases whose original support excludes the replaced root permit demotion.
This does not assert absence of Boolean-equivalent non-structural Directs.
"""
from __future__ import annotations
import argparse
import copy
import importlib
import json
from pathlib import Path
import shutil
import sys
import time
import traceback

from diagnostic import load_runtime, require, sha, write_json
from audit_products import validate_output
from audit_online_products import bind_files, verify_bound, existing_dsec_cache, seed_reused_dsec_cache, emit_product

HERE=Path(__file__).resolve().parent


class GlobalStructure:
    def __init__(self,p,a):
        self.p,self.a=p,a;self.structure=p.Structure(a);self.graph=p.Graph()
        self.mapped=[0]+[self.graph.pi()for _ in range(a.ni+a.nl)]
        for x,y in a.gates:
            self.mapped.append(self.graph.land(self.mapped[x//2]^(x&1),self.mapped[y//2]^(y&1)))
        self.aliases={}
        for node,value in enumerate(self.mapped):
            self.aliases.setdefault(value,[]).append(2*node)
            self.aliases.setdefault(value^1,[]).append(2*node+1)
        self.supports={}

    def support(self,node):
        if node not in self.supports:self.supports[node]=self.structure.tfi([node])
        return self.supports[node]

    def alias_info(self,value,root):
        all_aliases=self.aliases.get(value,[])
        safe=[lit for lit in all_aliases if root not in self.support(lit//2)]
        return dict(original_alias_literals=all_aliases,safe_original_alias_literals=safe,
            unsafe_root_dependent_alias_literals=[lit for lit in all_aliases if lit not in safe],
            later_safe_alias_literals=[lit for lit in safe if lit//2>root])

    def classify(self,c):
        p=self.p;root=c['root'];g=p.Graph();g.gates=list(self.graph.gates);g.hash=dict(self.graph.hash)
        boundary=len(g.gates);built=[];intermediate=[]
        def val(code):
            if code>=0:
                require(code//2<root,'candidate original divisor is not earlier than root')
                return self.mapped[code//2]^(code&1)
            require(code<=-2,'invalid recipe literal');node,phase=divmod(-code-2,2)
            require(node<len(built),'non-topological recipe');return built[node]^phase
        for i in range(0,len(c['recipe']),2):
            value=g.land(val(c['recipe'][i]),val(c['recipe'][i+1]));built.append(value)
            intermediate.append(dict(gate_index=i//2,canonical_literal=value,
                is_global_original_value=value//2<boundary,**self.alias_info(value,root)))
        output=val(c['out']);info=self.alias_info(output,root)
        live=set();todo=[output//2]
        while todo:
            node=todo.pop()
            if node in live:continue
            live.add(node)
            if g.gates[node]is not None:todo.extend(lit//2 for lit in g.gates[node])
        global_new_live=[n for n in live if n>=boundary]
        safe=info['safe_original_alias_literals']
        chosen=min(safe,key=lambda lit:(lit//2>=root,lit))if safe else None
        output_class=('NO_CONSTRUCTION_DIRECT'if not c['recipe']else
                      'WHOLE_ORIGINAL_EXISTING_OUTPUT_SAFE'if safe else
                      'WHOLE_ORIGINAL_ALIAS_ROOT_DEPENDENT_ONLY'if info['original_alias_literals']else
                      'NO_WHOLE_ORIGINAL_STRUCTURAL_OUTPUT_ALIAS')
        record=dict(root=root,recipe=c['recipe'],out=c['out'],classification=output_class,
            canonical_output=output,global_live_fresh_gates=len(global_new_live),
            selected_original_alias_literal=chosen,output_alias_is_later=(chosen//2>root)if chosen is not None else None,
            output_alias_is_originally_live=(chosen//2 in self.structure.live)if chosen is not None else None,
            output_alias_support=sorted(self.support(chosen//2))if chosen is not None else None,
            intermediate=intermediate,**info)
        if chosen is not None and c['recipe']:
            # The original Build witness must also separate root from this alias.
            witness=c['free_witness'];values=self.a.step(witness['inputs'],witness['state'])[2]
            recipe=p.recipe_eval(c['recipe'],c['out'],values);alias=values[chosen//2]^(chosen&1)
            require(recipe==alias and values[root]!=alias,'global alias/free witness replay failed')
            record['free_witness_alias_replay']=dict(status='PASS',root_value=values[root],alias_value=alias,
                witness_sha256=__import__('hashlib').sha256(json.dumps(witness,sort_keys=True).encode()).hexdigest())
        return record


def removal_set(selected,realization,classifications):
    by_root={r['root']:r for r in classifications};real={r['root']:r for r in realization}
    require(len(by_root)==len(selected)==len(real),'duplicate/missing selected root')
    genuinely_new=[];demoted=[]
    for c in selected:
        r=real[c['root']];prefix_fresh=bool(c['recipe'])and r['output_is_new']and r['output_is_live']and r['live_created_gates']>0
        if not prefix_fresh:continue
        if by_root[c['root']]['safe_original_alias_literals']:demoted.append(c)
        else:genuinely_new.append(c)
    roots={c['root']for c in genuinely_new}
    return genuinely_new,demoted,[c for c in selected if c['root']not in roots]


def audit_case(p,product,attribution,name,out,args,run,run_plan):
    start=time.monotonic();out.mkdir();prior=attribution/name;row=json.loads((prior/'result.json').read_text())
    require(row['status']=='ATTRIBUTION_AUDIT_COMPLETE','unverified source attribution')
    original_case=run/name;job=json.loads((original_case/'job.json').read_text());original_result=json.loads((original_case/'result.json').read_text())
    expected=row['input_sha256'];require(sha(prior/'input.aig')==expected,'source input changed')
    bound={};bind_files(bound,[prior/'result.json',prior/'input.aig',prior/'selected_builds.json',prior/'source_proof_validation.json',
        prior/'mixed/selection.json',prior/'mixed/product.aig',prior/'original_selected_replay.aig',original_case/'job.json',original_case/'result.json'])
    for path,digest in json.loads((prior/'source_manifest.json').read_text()).items():
        require(sha(path)==digest,'earlier attribution source changed');bound[path]=digest
    shutil.copyfile(prior/'input.aig',out/'input.aig');input_path=out/'input.aig'
    require(sha(input_path)==expected,'copied input mismatch');bind_files(bound,[input_path])
    a=p.Aiger(input_path);global_graph=GlobalStructure(p,a)
    checkpoint=Path(original_result['selected_checkpoint']['directory'])
    cache=existing_dsec_cache(product,original_result,original_case,checkpoint,run_plan['abc_sha256'],expected,bound)
    seed_reused_dsec_cache(product,prior,expected,run_plan['abc_sha256'],cache,bound)
    results={};all_classifications={}
    for label in ('original','mixed'):
        if label=='original':
            selected=json.loads((prior/'selected_builds.json').read_text());expected_product=prior/'original_selected_replay.aig'
        else:
            selected=json.loads((prior/'mixed/selection.json').read_text())['selected'];expected_product=prior/'mixed/product.aig'
        classification=[global_graph.classify(c)for c in selected]
        full=product.rebuild(a,selected)
        directory=out/label;directory.mkdir()
        digest=product.write_aig(directory/'full_replay.aig',full)
        require(digest==sha(expected_product),'full selected replay changed')
        write_json(directory/'classification.json',classification)
        fresh,demoted,without=removal_set(selected,full['realization'],classification)
        write_json(directory/'selected_sets.json',dict(original_selected=selected,genuinely_new_builds=fresh,
            global_existing_output_demotions=demoted,without_genuinely_new_build=without,
            rule='remove only actual prefix-fresh/live selected Builds with no root-independent whole-original structural output alias'))
        full_result,_=emit_product(product,a,selected,'full',directory,input_path,args.abc,args.dsec_seconds,cache,expected,run_plan['abc_sha256'])
        removed,_=emit_product(product,a,without,'without_genuinely_new_build',directory,input_path,args.abc,args.dsec_seconds,cache,expected,run_plan['abc_sha256'])
        marginal=removed['and_count']-full_result['and_count']
        results[label]=dict(selected=len(selected),prefix_fresh_builds=len(fresh)+len(demoted),
            whole_original_existing_output_demotions=len(demoted),whole_original_unaliased_builds=len(fresh),
            whole_original_unaliased_roots=[c['root']for c in fresh],demoted_roots=[c['root']for c in demoted],
            full=full_result,without_genuinely_new_build=removed,exact_same_selected_set_global_hash_corrected_build_marginal=marginal,
            validated_global_hash_corrected_build_marginal=marginal if full_result['dsec']['status']==removed['dsec']['status']=='PASS'else None)
        all_classifications[label]=classification
        write_json(directory/'result.json',results[label])
    require(sha(input_path)==expected,'copied input changed');verify_bound(bound)
    write_json(out/'source_manifest.json',bound)
    dsec_s=sum(r[k]['dsec']['charged_new_wall_s']for r in results.values()for k in ('full','without_genuinely_new_build'))
    final=dict(case=name,status='GLOBAL_STRUCTURAL_ALIAS_ACCOUNTING_COMPLETE',input_sha256=expected,loaded_and=row['loaded_and'],
        earlier_id_conditional_build_marginal=row['validated_conditional_fresh_build_marginal'],
        global_hash_corrected_conditional_build_marginal=results['mixed']['validated_global_hash_corrected_build_marginal'],
        products=results,additional_wall_s=time.monotonic()-start,new_dsec_wall_s=dsec_s,
        new_dsec_calls=sum(not r[k]['dsec']['reused_exact_graph_dsec']for r in results.values()for k in ('full','without_genuinely_new_build')),
        original_search_complete=row['original_search_complete'],original_evidence_unchanged=True,
        proof_queries_repeated=0,scope='whole-original structural hashing/folding and complemented outputs; root-independent aliases demoted with identical recipe materialization; not exhaustive Boolean Direct equivalence',
        native_novelty='NOT_CHECKED',same_original_transform_budget_claim=False)
    write_json(out/'result.json',final)
    print(json.dumps(dict(case=name,original_output_aliases=results['original']['whole_original_existing_output_demotions'],
        mixed_output_aliases=results['mixed']['whole_original_existing_output_demotions'],
        corrected_build_marginal=final['global_hash_corrected_conditional_build_marginal'],new_dsec_calls=final['new_dsec_calls'])),flush=True)
    return final


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--attribution',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--abc',type=Path,required=True);ap.add_argument('--dsec-seconds',type=float,default=120);args=ap.parse_args()
    attribution=args.attribution.resolve();args.out=args.out.resolve();args.abc=args.abc.resolve()
    prior_plan=json.loads((attribution/'plan.json').read_text());run=Path(prior_plan['source_run']);run_plan=json.loads((run/'plan.json').read_text())
    validate_output(args.out,attribution,run);require(json.loads((attribution/'integrity.json').read_text())['status']=='PASS','prior attribution integrity missing')
    bound={};bind_files(bound,[path for path in attribution.rglob('*')if path.is_file()])
    bind_files(bound,[Path(__file__),HERE/'diagnostic.py',HERE/'audit_products.py',HERE/'audit_online_products.py',run/'plan.json'])
    require(sha(args.abc)==run_plan['abc_sha256'],'ABC identity changed');bound[str(args.abc)]=run_plan['abc_sha256']
    for name,digest in run_plan['runtime_source_hashes'].items():bound[str(run/'source'/name)]=digest
    verify_bound(bound);p=load_runtime(run/'source');product=importlib.import_module('product')
    require(Path(product.__file__).resolve()==run/'source/nonlinear_divisors/product.py','wrong frozen product module')
    args.out.mkdir();(args.out/'source').mkdir()
    for path in (Path(__file__),HERE/'diagnostic.py',HERE/'audit_products.py',HERE/'audit_online_products.py'):
        shutil.copyfile(path,args.out/'source'/path.name)
    write_json(args.out/'plan.json',dict(source_attribution=str(attribution),source_run=str(run),source_and_helper_sha256=bound,
        classification='root-independent whole-original structural output aliases including later IDs and complements',
        construction_policy='unchanged recipe materialization; exact same-selection removal',scope_excludes_global_Boolean_equivalence=True))
    results=[]
    for row in json.loads((attribution/'results.json').read_text()):
        name=row['case']
        try:r=audit_case(p,product,attribution,name,args.out/name,args,run,run_plan)
        except Exception as error:
            r=dict(case=name,status='ERROR',error=repr(error));(args.out/name).mkdir(exist_ok=True)
            (args.out/name/'error.log').write_text(traceback.format_exc());write_json(args.out/name/'result.json',r);print(json.dumps(r),flush=True)
        results.append(r);write_json(args.out/'results.json',results)
    verify_bound(bound);write_json(args.out/'integrity.json',dict(status='PASS',source_and_helpers_unchanged=True))
    return int(any(r['status']=='ERROR'for r in results))


if __name__=='__main__':raise SystemExit(main())
