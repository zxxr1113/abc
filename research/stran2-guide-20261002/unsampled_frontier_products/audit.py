#!/usr/bin/env python3
"""PREPARATION unless independent boundary review and explicit parent GO are given."""
from __future__ import annotations
import argparse
import copy
import importlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
import traceback
from support import *
from certificates import verify_frontier_receipts
from proofs import fresh_proofs
from products import Products,run_selection_family,dominance
from run import accept_completed,supervise
import run as frontier_run
require(Path(frontier_run.__file__).resolve()==FRONTIER/'run.py','wrong frontier run module')
SCRATCH=Path('/workspace/scratch/7e0c7273599c')

def load_sources(args,out,deadline,launch):
    protocol=read(HERE/'protocol.json')
    require(source_manifest()==launch['source_manifest'],'audit source drift')
    require(audit_dependencies()==launch['dependencies'],'audit helper drift')
    require(frontier_common.digest(frontier_common.source_manifest())==protocol['source_manifest_sha256'],
            'frozen discovery implementation drift')
    require(sha(FRONTIER/'protocol.json')==protocol['source_protocol_sha256'],'discovery protocol drift')
    require(sha(args.diagnostic_review)==protocol['diagnostic_review_sha256']==launch['diagnostic_review_sha256'],
            'terminal independent diagnostic review changed')
    dr=read(args.diagnostic_review)
    require(dr['status']=='PASS' and dr['run']==protocol['source_run'] and
            dr['source_manifest_sha256']==protocol['source_manifest_sha256'],'wrong diagnostic review')
    source=Path(protocol['source_run']);case=source/protocol['case'];work=case/'work'
    reviewed_bindings=Bindings();bind_reviewed_run(dr,source,reviewed_bindings)
    accept_completed(protocol['case'],work,case,read(source/'source_manifest.json'))
    require(all(r['status']=='COMPLETE' for r in read(source/'summary.json')['cases']),'source diagnostic incomplete')
    frozen,baseline,snapshot,bindings=authenticate(protocol['case'],deadline)
    for path,expected in reviewed_bindings.files.items():bindings.add(path,expected)
    for path in sorted(source.rglob('*')):
        if path.is_file():bindings.add(path)
    for path,expected in dr['evidence'].items():bindings.add(path,expected)
    bindings.add(args.diagnostic_review,launch['diagnostic_review_sha256'])
    bindings.add(args.review,launch['audit_review_sha256'])
    for name,expected in launch['source_manifest'].items():bindings.add(HERE/name,expected)
    for path,expected in launch['dependencies'].items():bindings.add(path,expected)
    bindings.add(args.solver,protocol['solver_sha256']);bindings.add(str(args.solver)+'.build.json',protocol['solver_build_sha256'])
    build=read(str(args.solver)+'.build.json')
    require(build['schema']==2 and build['conflicts_per_query']==1000 and build['projection_phase']=='free','wrong bound solver')
    for path,expected in build['files'].items():bindings.add(path,expected)
    bindings.add(args.abc,protocol['abc_sha256'])
    for name,expected in frontier_common.source_manifest().items():bindings.add(FRONTIER/name,expected)
    p=load_runtime(frozen);product=importlib.import_module('product')
    product_path=Path(product.__file__).resolve()
    require(str(product_path) in frozen['source_hashes'] and sha(product_path)==frozen['source_hashes'][str(product_path)],
            'wrong frozen product implementation')
    inputpath=out/'input.aig';shutil.copyfile(frozen['input'],inputpath);bindings.add(inputpath,frozen['input_sha256'])
    a=p.Aiger(inputpath);ia=IndependentAig(inputpath);s=p.Structure(a)
    allnew=read(work/'proof/candidates.json')
    source_receipts=verify_frontier_receipts(p,a,ia,allnew,work/'proof',out,deadline)
    write_new(out/'source_frontier_receipt_replay.json',source_receipts)
    baseline_byid={cid(c):c for c in baseline}
    refs=read(work/'baseline_qualified_references.json');old=[]
    for ref in refs:
        root,recipe,output=ref['candidate_id'];identity=(root,tuple(recipe),output)
        require(identity in baseline_byid,'old qualified identity is not in original witnessed baseline')
        c=copy.deepcopy(baseline_byid[identity]);path=Path(ref['historical_certificate_file'])
        require(str(path) in frozen['source_hashes'] and sha(path)==ref['historical_certificate_sha256'],
                'old qualified proof reference changed')
        matches=[r for r in read(path) if cid(r)==identity]
        require(len(matches)==1 and matches[0]['qualified_offline_opportunity'],'old qualified reference missing')
        c['proof']=copy.deepcopy(matches[0].get('diagnostic_proof',matches[0].get('proof')))
        require(c['proof']['free']=='SAT' and c['proof']['reset']=='UNSAT' and
                c['proof'].get('image',c['proof'].get('step'))=='UNSAT','old qualified status mismatch')
        c['audit_origin']='old49';c['historical_certificate_reference']=ref;old.append(c)
    new=[copy.deepcopy(c) for c in allnew if c['qualified_offline_opportunity']]
    for c in new:c['audit_origin']='new55_unsampled'
    require(len(old)==49 and len(new)==55 and not {cid(c) for c in old}&{cid(c) for c in new},'old49/new55 membership changed')
    union=old+new;require(len({cid(c) for c in union})==104,'cumulative104 does not preserve exact identities')
    for c in union:
        verify_candidate(p,s,ia,c)
        if c['audit_origin']=='new55_unsampled':
            require('witness_lane' not in c and c['free_witness']['kind']=='candidate_local_free_SAT' and
                    c['free_witness']['global_lane'] is None,'new free witness was converted to a fabricated lane')
    export=read(source/'newly_qualified_identities.json')
    require({(r['root'],tuple(r['recipe']),r['out']) for r in export if r['case']==protocol['case']}=={cid(c) for c in new},
            'new identity export differs')
    write_new(out/'candidate_sets.before_fresh_proof.json',dict(old=old,new=new,cumulative=union))
    bindings.check(deadline)
    global_module=module('audit_original_hash',PACKAGE/'global_expression_review/review.py')
    hashdirect=module('audit_hash_direct',PACKAGE/'nonlinear_divisors/hash_direct_audit.py')
    return protocol,frozen,bindings,p,product,a,ia,s,inputpath,union,{cid(c) for c in new},global_module,hashdirect

def calculate_changes(old,union):
    a={cid(c) for c in old};b={cid(c) for c in union}
    def ids(values):return [[x[0],list(x[1]),x[2]] for x in sorted(values)]
    return dict(retained=ids(a&b),removed=ids(a-b),added=ids(b-a),
                old_roots=sorted({x[0] for x in a}),union_roots=sorted({x[0] for x in b}))

def worker(args,launch):
    out=args.out/'work';out.mkdir();started=time.monotonic();deadline=Deadline(args.deadline)
    try:
        protocol,frozen,bindings,p,product,a,ia,s,inputpath,union,newids,global_module,hashdirect=load_sources(args,out,deadline,launch)
        timings={'preparation_wall_s':time.monotonic()-started}
        phase=time.monotonic();proved,buildreport=fresh_proofs(p,a,ia,union,args.solver,out/'fresh_build_proofs',deadline,bindings,True)
        timings['fresh_build_proof_wall_s']=time.monotonic()-phase
        old=[c for c in proved if cid(c) not in newids];arms={'old49':old,'union104':proved}
        require(len(old)==49 and len(proved)==104,'fresh proof changed cumulative membership')
        original=global_module.OriginalHash(global_module.Aig(inputpath));classifications={cid(c):classify(original,s,c) for c in proved}
        write_new(out/'whole_original_classification.json',list(classifications.values()))
        selections={};selection_records={}
        for arm,candidates in arms.items():
            chosen,rejected=product.select(s,candidates,deadline);selections[arm]=chosen
            selection_records[arm]=dict(selected=chosen,rejected=rejected)
        write_new(out/'raw_selections.json',selection_records)
        pools={r['root']:r['pool'] for r in frozen['roots']}
        phase=time.monotonic();directs,scope=direct_scope(p,s,hashdirect,selections,pools,2)
        # Optional sampled Direct witnesses are independently checked; missing a
        # sampled free witness never filters an otherwise valid Direct alternative.
        for c in directs:
            diff=frozen['initial_free_signatures'][c['root']]^p.recipe_eval([],c['out'],frozen['initial_free_signatures'],frozen['initial_free_mask'])
            if diff:
                c['witness_lane']=(diff&-diff).bit_length()-1
                c['free_witness']=p.witness(a,c,frozen['initial_free_signatures'])
        write_new(out/'shared_direct_scope.json',scope)
        directvalid,directreport=fresh_proofs(p,a,ia,directs,args.solver,out/'fresh_direct_proofs',deadline,bindings,False)
        timings['direct_scope_and_proof_wall_s']=time.monotonic()-phase
        emitter=Products(p,product,a,ia,global_module,inputpath,args.abc,out,deadline,bindings)
        phase=time.monotonic();baseline,_=emitter.emit('baseline',[])
        selected_direct,rejected_direct=product.select(s,directvalid,deadline)
        directonly,_=emitter.emit('direct_only',selected_direct)
        write_new(out/'shared_direct_selection.json',dict(selected=selected_direct,rejected=rejected_direct))
        results={};mixedsets={};dominance_sets=[]
        for arm,candidates in arms.items():
            raw=selections[arm]
            raw_result=run_selection_family(p,s,product,emitter,arm+'/raw',raw,classifications,newids)
            mixed,rejected=product.select(s,directvalid+raw,deadline);mixedsets[arm]=mixed
            mixed_result=run_selection_family(p,s,product,emitter,arm+'/mixed',mixed,classifications,newids)
            results[arm]=dict(qualified_candidates=len(candidates),raw=raw_result,mixed=mixed_result,
                mixed_rejections=rejected,raw_cleanup_gain=baseline['and_count']-raw_result['products']['full']['and_count'],
                mixed_cleanup_gain=baseline['and_count']-mixed_result['products']['full']['and_count'])
            dominance_sets += [(arm+'/raw',raw,raw_result['products']['full']),(arm+'/mixed',mixed,mixed_result['products']['full'])]
        timings['primary_products_wall_s']=time.monotonic()-phase
        phase=time.monotonic();direct_dominance={}
        for label,selected,full in dominance_sets:
            direct_dominance[label]=dominance(p,s,product,emitter,'dominance/'+label,selected,directvalid,full)
        timings['direct_dominance_wall_s']=time.monotonic()-phase
        changes=dict(candidates=calculate_changes(old,proved),raw_selected=calculate_changes(selections['old49'],selections['union104']),
                     mixed_selected=calculate_changes(mixedsets['old49'],mixedsets['union104']))
        require(not changes['candidates']['removed'] and len(changes['candidates']['retained'])==49 and len(changes['candidates']['added'])==55,
                'cumulative identity preservation failed')
        write_new(out/'candidate_and_selection_changes.json',changes)
        dsec=emitter.cost_summary();bindings.check(deadline);emitter.emitted.check(deadline);deadline.remaining()
        result=dict(schema=1,status='EXTRA_COST_PRODUCT_AUDIT_COMPLETE',case='045_mem_ctrl',
            arms=results,baseline=baseline,direct_only=directonly,source_bindings=bindings.files,
            emitted_product_bindings=emitter.emitted.files,
            cumulative_preservation='old49 retained exactly;55 identities added',raw_candidate_changes=changes,
            original_input_and=a.na,empty_selection_and=baseline['and_count'],baseline_cleanup_delta=a.na-baseline['and_count'],
            direct_scope_roots=len(scope),direct_candidates=len(directs),proved_positive_directs=len(directvalid),
            hash_extra_direct_literals=sum(len(x['hash_extras']) for x in scope),
            new_global_output_alias_identities=sum(bool(classifications[i]['safe_original_aliases']) for i in newids),
            proof_reports=dict(Build=buildreport,Direct=directreport),timings=timings,**dsec,
            paired_raw_product_improvement=results['union104']['raw_cleanup_gain']-results['old49']['raw_cleanup_gain'],
            paired_mixed_product_improvement=results['union104']['mixed_cleanup_gain']-results['old49']['mixed_cleanup_gain'],
            paired_all_genuine_Build_marginal_difference=results['union104']['mixed']['all_genuine_build_same_set_marginal']-
                results['old49']['mixed']['all_genuine_build_same_set_marginal'],
            direct_dominance=direct_dominance,extra_worker_wall_s=time.monotonic()-started,
            same_original120s_budget=False,global_Boolean_Direct_exhaustion=False,native_novelty='NOT_CHECKED',
            policy_stops_here=True,no_online_or_full_cohort_run=True,
            output_artifacts={str(f.relative_to(out)):sha(f) for f in sorted(out.rglob('*')) if f.is_file()})
        write_new(out/'result.json',result);deadline.remaining()
        print(json.dumps(dict(status='COMPLETE',case='045_mem_ctrl',result_sha256=sha(out/'result.json'))),flush=True)
        return 0
    except BaseException as e:
        write_new(out/'failure.json',dict(status='TIMEOUT' if isinstance(e,(TimeoutError,subprocess.TimeoutExpired)) else 'ERROR',error=repr(e),
            traceback=traceback.format_exc(),extra_worker_wall_s=time.monotonic()-started))
        print(json.dumps(dict(status='ERROR',failure_sha256=sha(out/'failure.json'))),flush=True);return 2

def accept(out,launch):
    out=Path(out);work=out/'work';notices=[]
    for line in (out/'worker.log').read_text().splitlines():
        try:row=json.loads(line)
        except json.JSONDecodeError:continue
        if isinstance(row,dict) and row.get('status')=='COMPLETE':notices.append(row)
    require(len(notices)==1 and notices[0].get('case')=='045_mem_ctrl','missing or duplicate completion')
    require(sha(work/'result.json')==notices[0]['result_sha256'],'completion result changed')
    result=read(work/'result.json');require(result['status']=='EXTRA_COST_PRODUCT_AUDIT_COMPLETE','bad result status')
    actual={str(f.relative_to(work)):sha(f) for f in sorted(work.rglob('*')) if f.is_file() and str(f.relative_to(work))!='result.json'}
    require(actual==result['output_artifacts'],'product artifact tree changed')
    require(source_manifest()==launch['source_manifest'] and audit_dependencies()==launch['dependencies'],'audit implementation drift')
    Bindings(result['source_bindings']).check();Bindings(result['emitted_product_bindings']).check()
    for label,directory in [('Build','fresh_build_proofs'),('Direct','fresh_direct_proofs')]:
        report=result['proof_reports'][label]
        require(read(work/directory/'report.json')==report,'persisted proof report differs from completion')
        Bindings(report['proof_bindings']).check()
    require(result['arms']['old49']['qualified_candidates']==49 and result['arms']['union104']['qualified_candidates']==104,'candidate count changed')
    for arm in result['arms'].values():
        for family in ('raw','mixed'):
            for graph in arm[family]['products'].values():require(graph['dsec']['status']=='PASS','unvalidated primary product')
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--solver',type=Path,required=True);ap.add_argument('--abc',type=Path,required=True)
    ap.add_argument('--diagnostic-review',type=Path,required=True);ap.add_argument('--review',type=Path,required=True)
    ap.add_argument('--parent-go',choices=['RUN_MEM_ATTRIBUTION']);ap.add_argument('--worker',action='store_true');ap.add_argument('--deadline',type=float)
    args=ap.parse_args();args.out=args.out.resolve();args.solver=args.solver.resolve();args.abc=args.abc.resolve()
    if args.worker:
        require(args.deadline is not None,'worker deadline missing');return worker(args,read(args.out/'launch.json'))
    protocol=read(HERE/'protocol.json');review=read(args.review)
    require(args.parent_go=='RUN_MEM_ATTRIBUTION','explicit parent GO required')
    require(args.out.parent==SCRATCH and not args.out.exists() and not args.out.is_relative_to(Path(protocol['source_run']))
            and not args.out.is_relative_to(HERE) and not args.out.is_relative_to(FRONTIER),'new scratch output outside evidence/source required')
    manifest=source_manifest();deps=audit_dependencies()
    require(review['status']=='PASS' and review['source_manifest_sha256']==digest(manifest) and review['protocol_sha256']==sha(HERE/'protocol.json')
        and review['dependencies']==deps,'audit source/protocol/helper review mismatch')
    require(sha(args.diagnostic_review)==protocol['diagnostic_review_sha256']==review['diagnostic_review_sha256'],'diagnostic review mismatch')
    require(sha(args.solver)==protocol['solver_sha256']==review['solver_sha256'] and
        sha(str(args.solver)+'.build.json')==protocol['solver_build_sha256']==review['solver_build_sha256'] and
        sha(args.abc)==protocol['abc_sha256']==review['abc_sha256'],'reviewed tool mismatch')
    args.out.mkdir();launch=dict(source_manifest=manifest,dependencies=deps,protocol=protocol,
        audit_review_sha256=sha(args.review),diagnostic_review_sha256=sha(args.diagnostic_review),
        solver_sha256=sha(args.solver),solver_build_sha256=sha(str(args.solver)+'.build.json'),abc_sha256=sha(args.abc),
        parent_go=args.parent_go,extra_cost=True)
    write_new(args.out/'launch.json',launch)
    supervisor=supervise(lambda end:[sys.executable,'-B',str(HERE/'audit.py'),'--worker','--deadline',str(end),
        '--out',str(args.out),'--solver',str(args.solver),'--abc',str(args.abc),'--diagnostic-review',str(args.diagnostic_review),
        '--review',str(args.review)],args.out,protocol['total_audit_wall_seconds'])
    start=time.monotonic();status='TIMEOUT' if supervisor['timed_out'] else 'ERROR' if supervisor['returncode'] else 'COMPLETE'
    if status=='COMPLETE':
        try:accept(args.out,launch)
        except BaseException as e:
            status='ERROR';write_new(args.out/'acceptance_failure.json',dict(error=repr(e),traceback=traceback.format_exc()))
    write_new(args.out/'supervisor.json',dict(status=status,supervisor=supervisor,post_acceptance_wall_s=time.monotonic()-start,
        policy_stops_here=True,no_online_or_full_cohort_run=True))
    print(json.dumps(read(args.out/'supervisor.json')),flush=True);return 0 if status=='COMPLETE' else 2
if __name__=='__main__':raise SystemExit(main())
