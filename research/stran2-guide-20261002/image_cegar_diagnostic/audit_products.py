#!/usr/bin/env python3
"""Extra-cost exact products and bounded Direct sensitivity for frozen diagnostic.

No search extension, runtime edit, native-novelty claim, or original-budget claim.
Reconstructs saved proof receipts, repeats qualified triples in a fresh solver,
and uses byte-identical stable product selection/replay. Every output is new.
"""
from __future__ import annotations
import argparse
import copy
import csv
import importlib
import json
from pathlib import Path
import shutil
import sys
import time
import traceback

from diagnostic import candidate_id, load_runtime, require, sha, verify_source, write_json


def tree_hashes(root):
    return {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob('*')) if p.is_file()}


def validate_output(out, diagnostic, run):
    require(not out.exists(), 'new output directory required')
    for source in (diagnostic, run):
        require(not out.resolve().is_relative_to(source.resolve()), 'output must be outside all source evidence')


def query_text(queries):
    return str(len(queries)) + '\n' + ''.join(
        f'{i} {len(q)} ' + ' '.join(map(str, q)) + '\n' for i, q in enumerate(queries))


def append_triples(p, graph, mappings, candidates):
    queries, order = [], []
    for i, c in enumerate(candidates):
        for phase, mapping in mappings:
            expr = p.graph_recipe(graph, mapping, c['recipe'], c['out'])
            miter = graph.xor(mapping[c['root']], expr)
            order.append(dict(query=len(queries), candidate=i, root=c['root'],
                              recipe=c['recipe'], out=c['out'], phase=phase, miter_literal=miter))
            queries.append([miter])
    return queries, order


def verify_diagnostic_receipts(p, graph, mappings, old, diagnostic, out):
    """Match CNF, query bytes, row identity, statuses and independent witnesses."""
    new = json.loads((diagnostic / 'new_proofs/candidates.json').read_text())
    for c in old:
        if c['proof']['step'] == 'SAT':
            expr = p.graph_recipe(graph, dict(mappings)['step'], c['recipe'], c['out'])
            graph.xor(dict(mappings)['step'][c['root']], expr)
    queries, order = append_triples(p, graph, mappings, new)
    graph.cnf(out / 'diagnostic_reconstructed.cnf')
    (out / 'diagnostic_reconstructed.queries').write_text(query_text(queries))
    report = json.loads((diagnostic / 'new_proofs/report.json').read_text())
    for name, key in [('obligations.cnf', 'cnf_sha256'), ('obligations.queries', 'queries_sha256'),
                      ('obligations.results.csv', 'results_sha256')]:
        require(sha(diagnostic / 'new_proofs' / name) == report[key], 'diagnostic receipt hash mismatch')
    require(sha(out / 'diagnostic_reconstructed.cnf') == report['cnf_sha256'], 'diagnostic CNF reconstruction mismatch')
    require(sha(out / 'diagnostic_reconstructed.queries') == report['queries_sha256'], 'diagnostic query reconstruction mismatch')
    with (diagnostic / 'new_proofs/obligations.results.csv').open() as stream:
        rows = list(csv.DictReader(stream))
    require([int(r['query']) for r in rows] == list(range(len(queries))), 'diagnostic result row identity mismatch')
    names = {-1: 'UNSAT', 0: 'UNKNOWN', 1: 'SAT'}
    for i, c in enumerate(new):
        triple = [int(r['result']) for r in rows[3*i:3*i+3]]
        require(all(v in names for v in triple), 'invalid diagnostic status')
        require(c['diagnostic_proof'] == dict(zip(('free', 'reset', 'image'), map(names.get, triple))), 'saved diagnostic proof disagrees with raw results')
        require(c['qualified_offline_opportunity'] == (triple == [1,-1,-1]), 'saved diagnostic qualification mismatch')
    write_json(out / 'diagnostic_query_order.json', order)
    return new


def check_candidate(p, a, s, c, free):
    root = c['root']
    require(s.nci < root <= a.m and root in s.live, 'invalid root')
    normalized = p.normalize(s, root, c['recipe'], c['out'])
    require(normalized == (c['recipe'], c['out']) and bool(c['recipe']), 'unnormalized or Direct Build')
    cost = s.cost(root, c['recipe'], c['out'])
    require(cost['conservative_gain'] > 0 and all(c[k] == v for k,v in cost.items()), 'candidate cost mismatch')
    witness = p.witness(a, c, free)
    if 'free_witness' in c:
        require(c['free_witness'] == witness, 'saved free witness mismatch')
    c['free_witness'] = witness


def fresh_recheck(p, a, s, candidates, cfg, solver, out, seconds):
    out.mkdir()
    graph, base, step, reset = p.compile_graph(a)
    (free, _, _), _ = p.signatures(graph, [base, step, reset], cfg)
    for c in candidates:
        check_candidate(p, a, s, c, free)
    queries, order = append_triples(p, graph, [('free',base),('reset',reset),('step',step)], candidates)
    answers, report = p.run_queries(graph, queries, out, solver, p.Deadline(seconds))
    write_json(out / 'query_order.json', order)
    for i,c in enumerate(candidates):
        triple = answers[3*i:3*i+3]
        require(triple[0] != -1 and triple[1] != 1 and triple[2] != 1, 'fresh result contradicts saved certificate')
        status = {-1:'UNSAT',0:'UNKNOWN',1:'SAT'}
        c['proof'] = dict(zip(('free','reset','step'), map(status.get,triple)))
        c['proof'].update(free_witness_replayed=True, extra_cost_fresh_solver_recheck=True,
                          sequential_relation='PROVED_RESET_IMAGE' if triple == [1,-1,-1] else 'NOT_PROVED')
        c['qualified_offline_opportunity'] = triple == [1,-1,-1]
    write_json(out / 'candidates.json', candidates)
    write_json(out / 'report.json', report)
    return candidates, report, free


def replay_selected(product, a, chosen, out, input_path, abc, seconds, tag):
    out.mkdir()
    rebuilt = product.rebuild(a, chosen)
    digest = product.write_aig(out / 'product.aig', rebuilt)
    write_json(out / 'selection.json', dict(selected=chosen, realization=rebuilt['realization']))
    result = dict(and_count=len(rebuilt['gates']), sha256=digest, selected=len(chosen),
                  dsec=product.dsec(abc,input_path,out/'product.aig',out,seconds,tag))
    write_json(out / 'result.json',result)
    return result, rebuilt


def direct_sensitivity(p, product, a, s, selected, roots, cfg, solver, abc, input_path, out, seconds, dsec_seconds):
    """All constants and both phases of saved pools/used divisors, selected roots only."""
    out.mkdir()
    pools = {row['root']:row['pool'] for row in roots}
    graph, base, step, reset = p.compile_graph(a)
    (free, _, _), free_mask = p.signatures(graph,[base,step,reset],cfg)
    direct = []
    for c in selected:
        root = c['root']
        nodes = sorted(set(pools[root]) | p.external_nodes(c['recipe'],c['out']))
        require(all(0 < n < root for n in nodes), 'Direct pool contains illegal divisor')
        for lit in [0,1] + [2*n+phase for n in nodes for phase in (0,1)]:
            d = dict(root=root,recipe=[],out=lit,divisors=[] if lit < 2 else [lit//2],
                     **s.cost(root,[],lit))
            mismatch = free[root] ^ p.recipe_eval([],lit,free,free_mask)
            if mismatch:
                d['witness_lane'] = (mismatch & -mismatch).bit_length()-1
                d['free_witness'] = p.witness(a,d,free)
            direct.append(d)
    queries, order = append_triples(p,graph,[('free',base),('reset',reset),('step',step)],direct)
    proofdir=out/'proofs'; proofdir.mkdir()
    answers,stats=p.run_queries(graph,queries,proofdir,solver,p.Deadline(seconds))
    write_json(proofdir/'query_order.json',order)
    valid=[]
    for i,d in enumerate(direct):
        triple=answers[3*i:3*i+3]
        d['proof']=dict(zip(('free','reset','step'),({-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[v] for v in triple)))
        require(not (triple[0]==-1 and 'free_witness' in d),'Direct free UNSAT contradicts replay')
        d['sequentially_proved']=triple[1:]==[-1,-1]
        if d['sequentially_proved'] and d['conservative_gain']>0: valid.append(d)
    write_json(proofdir/'candidates.json',direct);write_json(proofdir/'report.json',stats)
    baseline=product.rebuild(a,[]); baseline_and=len(baseline['gates'])
    comparisons=[]
    for c in selected:
        ds=[d for d in valid if d['root']==c['root']]
        build_gain=baseline_and-len(product.rebuild(a,[c])['gates'])
        rows=[]
        for d in ds:
            rows.append(dict(out=d['out'],conservative_gain=d['conservative_gain'],
                             retained_mffc_nodes=d['retained_mffc_nodes'],
                             exact_single_replacement_gain=baseline_and-len(product.rebuild(a,[d])['gates']),
                             free=d['proof']['free']))
        best=max((r['exact_single_replacement_gain'] for r in rows),default=None)
        comparisons.append(dict(root=c['root'],build_conservative_gain=c['conservative_gain'],
            build_exact_single_replacement_gain=build_gain,direct_relations=rows,best_direct_exact_gain=best,
            direct_weakly_dominates_single_replacement=best is not None and best>=build_gain,
            scope='constants and both phases of exact saved pool plus used divisors; this selected root only'))
    write_json(out/'per_root_comparison.json',comparisons)
    arms={}
    selections={}
    for name,cs in [('direct_only',valid),('mixed_selected_builds_and_direct',valid+selected)]:
        chosen,rejected=product.select(s,cs)
        result,rebuilt=replay_selected(product,a,chosen,out/name,input_path,abc,dsec_seconds,'dsec')
        result.update(exact_gain=baseline_and-result['and_count'], rejected=rejected)
        write_json(out/name/'result.json',result);arms[name]=result; selections[name]=(chosen,rebuilt)
    chosen,rebuilt=selections['mixed_selected_builds_and_direct']
    realized={r['root']:r for r in rebuilt['realization']}
    actual_build=[c for c in chosen if c['recipe'] and realized[c['root']]['output_is_new'] and
                  realized[c['root']]['output_is_live'] and realized[c['root']]['live_created_gates']>0]
    build_roots={c['root'] for c in actual_build}
    without=[c for c in chosen if c['root'] not in build_roots]
    removed,_=replay_selected(product,a,without,out/'mixed_without_actual_build',input_path,abc,dsec_seconds,'dsec')
    arms['mixed_without_actual_build']=removed
    marginal=removed['and_count']-arms['mixed_selected_builds_and_direct']['and_count']
    result=dict(scope='selected combined Build roots only; exact saved pools, used divisors, constants and both phases',
        candidates=len(direct),queries=stats,proved_positive_direct=len(valid),
        roots_with_proved_direct=len({c['root'] for c in valid}),
        roots_direct_weakly_dominates_single_replacement=sum(r['direct_weakly_dominates_single_replacement'] for r in comparisons),
        selected_build_roots=len(selected),arms=arms,actual_builds_in_mixed=len(actual_build),
        exact_same_mixed_selected_set_build_marginal=marginal,
        validated_build_marginal=(marginal if all(v['dsec']['status']=='PASS' for v in arms.values()) else None),
        exhaustive_global_direct_search=False,native_novelty='NOT_CHECKED')
    write_json(out/'result.json',result)
    return result


def audit_case(p,product,run,diagnostic,name,out,solver,abc,seconds,dsec_seconds):
    start=time.monotonic();out.mkdir()
    source=run/name; diag=diagnostic/name
    job=json.loads((source/'job.json').read_text());cfg=p.Config(**job['config'])
    input_path=Path(job['case']['input']);input_hash=job['case']['input_sha256']
    require(sha(input_path)==input_hash,'input identity mismatch')
    shutil.copyfile(input_path,out/'input.aig');input_path=out/'input.aig'
    evidence={**{str(diag/k):sha(diag/k) for k in ('provenance.json','refined_candidates.json','result.json')},
              **{str(source/k):sha(source/k) for k in ('job.json','root_search.jsonl','chunks/chunk_00000/candidates.json')}}
    roots=[json.loads(line) for line in (source/'root_search.jsonl').read_text().splitlines()][:32]
    old=json.loads((source/'chunks/chunk_00000/candidates.json').read_text())
    a=p.Aiger(input_path);s=p.Structure(a);graph,base,step,reset=p.compile_graph(a)
    evidence.update({str(k):v for k,v in verify_source(p,run,source,job,old,graph,
        dict(free=base,reset=reset,step=step),out,solver).items()})
    saved=json.loads((diag/'provenance.json').read_text())
    require(saved['input_sha256']==input_hash and saved['source_candidates_sha256']==sha(source/'chunks/chunk_00000/candidates.json')
            and saved['source_roots_sha256']==sha(source/'root_search.jsonl') and saved['source_runtime_sha256']==sha(p.__file__),
            'diagnostic source provenance mismatch')
    new=verify_diagnostic_receipts(p,graph,[('free',base),('reset',reset),('step',step)],old,diag,out)
    refined=json.loads((diag/'refined_candidates.json').read_text())
    refined_ids={candidate_id(c) for c in refined}
    old_ids={candidate_id(c) for c in old}
    old_good=[copy.deepcopy(c) for c in old if c['qualified_offline_opportunity'] and candidate_id(c) in refined_ids]
    new_good=[copy.deepcopy(c) for c in new if c['qualified_offline_opportunity'] and candidate_id(c) in refined_ids]
    require(not any(candidate_id(c) in old_ids for c in new_good),'new certificate is not new relative to source top-k')
    for c in old_good:c['audit_origin']='old_topk'
    for c in new_good:c['audit_origin']='image_cegar_new_topk'
    all_candidates,proof_report,_=fresh_recheck(p,a,s,old_good+new_good,cfg,solver,out/'fresh_recheck',seconds)
    qualified=[c for c in all_candidates if c['qualified_offline_opportunity']]
    arms={}
    for label,candidates in [('old_only',[c for c in qualified if c['audit_origin']=='old_topk']),
                             ('new_only',[c for c in qualified if c['audit_origin']=='image_cegar_new_topk']),
                             ('combined',qualified)]:
        arm=out/label;arm.mkdir()
        arms[label]=product.create_product(input_path,candidates,arm,abc,dsec_seconds,expected_input_sha256=input_hash)
    chosen=json.loads((out/'combined/selection.json').read_text())['selected']
    without=[c for c in chosen if c['audit_origin']!='image_cegar_new_topk']
    replay,_=replay_selected(product,a,without,out/'combined_without_new',input_path,abc,dsec_seconds,'dsec')
    exact_new_marginal=replay['and_count']-arms['combined']['product_and']
    sensitivity=direct_sensitivity(p,product,a,s,chosen,roots,cfg,solver,abc,input_path,out/'direct_sensitivity',seconds,dsec_seconds)
    for path,expected in evidence.items():require(sha(path)==expected,'source evidence changed during audit')
    write_json(out/'evidence_manifest.json',evidence)
    dsec_wall=sum(v[k]['wall_s'] for v in arms.values() for k in ('baseline_dsec','independent_dsec'))+replay['dsec']['wall_s']
    dsec_wall+=sum(v['dsec']['wall_s'] for v in sensitivity['arms'].values())
    total=time.monotonic()-start
    result=dict(case=name,status='EXTRA_COST_PRODUCT_AUDIT_COMPLETE',input_sha256=input_hash,
        loaded_and=job['case']['loaded_AND'],old_qualified=len(old_good),new_qualified=len(new_good),
        fresh_qualified=len(qualified),fresh_queries=proof_report,products=arms,
        combined_without_new=replay,exact_new_marginal_in_same_combined_selected_set=exact_new_marginal,
        validated_new_marginal=(exact_new_marginal if replay['dsec']['status']=='PASS' and
            arms['combined']['validated_standalone_noncomb_build_gain'] is not None else None),
        direct_sensitivity=sensitivity,extra_wall_s=total,extra_non_dsec_wall_s=total-dsec_wall,
        same_original_120s_budget=False,original_evidence_unchanged=True,native_novelty='NOT_CHECKED',
        diagnostic_scope='first 32 roots; extra-cost refinement and audit, not a reachable teacher')
    write_json(out/'result.json',result)
    print(json.dumps(dict(case=name,combined_gain=arms['combined']['validated_standalone_noncomb_build_gain'],
        new_marginal=result['validated_new_marginal'],direct_gain=sensitivity['arms']['direct_only']['exact_gain'],
        mixed_build_marginal=sensitivity['validated_build_marginal'],extra_wall_s=total)),flush=True)
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--diagnostic',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--solver',type=Path,required=True);ap.add_argument('--abc',type=Path,required=True)
    ap.add_argument('--case',action='append',choices=['045_mem_ctrl','060_wb_dma'])
    ap.add_argument('--proof-seconds',type=float,default=120);ap.add_argument('--dsec-seconds',type=float,default=120)
    args=ap.parse_args()
    plan=json.loads((args.diagnostic/'plan.json').read_text());run=Path(plan['run'])
    validate_output(args.out,args.diagnostic,run)
    args.out.mkdir(parents=True)
    original_tree=tree_hashes(args.diagnostic)
    for name,expected in json.loads((args.diagnostic/'source_manifest.json').read_text()).items():
        require(sha(args.diagnostic/'source'/name)==expected,'saved diagnostic source changed')
    require(sha(args.diagnostic/'source/diagnostic.py')==plan['diagnostic_sha256'],'diagnostic implementation identity mismatch')
    diagnostic_source=Path(__file__).resolve().parent/'diagnostic.py'
    require(sha(diagnostic_source)==plan['diagnostic_sha256'],'imported diagnostic helper identity mismatch')
    p=load_runtime(run/'source');product=importlib.import_module('product')
    stable=Path(__file__).resolve().parent.parent/'nonlinear_divisors/product.py'
    require(sha(stable)==sha(product.__file__),'stable product runtime mismatch')
    require(sha(args.solver)==plan['solver_sha256'],'solver identity mismatch')
    provenance=dict(schema=1,diagnostic=str(args.diagnostic.resolve()),run=str(run.resolve()),
        original_diagnostic_tree=original_tree,helper_sha256=sha(__file__),product_sha256=sha(product.__file__),
        diagnostic_helper_sha256=sha(diagnostic_source),
        solver_sha256=sha(args.solver),abc_sha256=sha(args.abc),same_original_120s_budget=False,
        native_novelty='NOT_CHECKED',cases=args.case or ['045_mem_ctrl','060_wb_dma'])
    write_json(args.out/'provenance.json',provenance)
    (args.out/'source').mkdir()
    for path in (Path(__file__).resolve(),diagnostic_source):
        shutil.copyfile(path,args.out/'source'/path.name)
    rows=[]
    for name in provenance['cases']:
        try: result=audit_case(p,product,run,args.diagnostic,name,args.out/name,args.solver.resolve(),args.abc.resolve(),args.proof_seconds,args.dsec_seconds)
        except Exception as error:
            result=dict(case=name,status='ERROR',error=repr(error),validated_gain=None)
            (args.out/name/'error.log').write_text(traceback.format_exc());write_json(args.out/name/'result.json',result)
            print(json.dumps(result),flush=True)
        rows.append(result);write_json(args.out/'results.json',rows)
    require(tree_hashes(args.diagnostic)==original_tree,'original diagnostic evidence changed')
    require(sha(__file__)==provenance['helper_sha256'] and sha(diagnostic_source)==provenance['diagnostic_helper_sha256'] and
            sha(args.solver)==provenance['solver_sha256'] and
            sha(args.abc)==provenance['abc_sha256'],'audit source/executable changed')
    write_json(args.out/'integrity.json',dict(status='PASS',original_diagnostic_unchanged=True))
    return 1 if any(r['status']=='ERROR' for r in rows) else 0


if __name__=='__main__':raise SystemExit(main())
