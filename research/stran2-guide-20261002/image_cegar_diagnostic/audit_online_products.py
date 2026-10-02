#!/usr/bin/env python3
"""Extra-cost, matched-grammar Direct attribution of completed online checkpoints.

Read-only source evidence; never changes the original transform outcome or runtime.
Reuses original Build proof receipts only after exact CNF reconstruction. New Direct
queries share conclusive results only for an identical frozen CNF/assumption tuple.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
import copy
import csv
import importlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import time
import traceback

import diagnostic as audit_diagnostic
from diagnostic import load_runtime, require, sha, write_json
from audit_products import append_triples, check_candidate, validate_output

HERE=Path(__file__).resolve().parent
_bound_runtime_diagnostic=None


def verify_bound(bound):
    for path,digest in bound.items():require(sha(path)==digest,'bound artifact changed: '+str(path))


def bind_files(bound,paths):
    for path in paths:
        path=Path(path).resolve();digest=sha(path)
        require(str(path) not in bound or bound[str(path)]==digest,'artifact changed before binding')
        bound[str(path)]=digest


def bind_runtime_model_replay(source,source_hashes,bound):
    """Bind the authenticated run-local replay module before inline imports.

    The CLI's audit helpers intentionally keep their original function globals.
    Only the conventional ``diagnostic`` import name is rebound, so the frozen
    runtime's strict same-source path guard remains effective. A third-party
    cached module is rejected rather than silently replaced.
    """
    global _bound_runtime_diagnostic
    source=Path(source).resolve();name='image_cegar_diagnostic/diagnostic.py'
    target=source/name;expected=source_hashes.get(name)
    require(type(expected)is str and len(expected)==64,'missing frozen model replay hash')
    require(target.resolve()==target,'frozen model replay path is not canonical')
    require(sha(target)==expected,'frozen model replay hash mismatch before import')
    bind_files(bound,[target])
    cached=sys.modules.get('diagnostic')
    require(cached is audit_diagnostic or
            (cached is not None and cached is _bound_runtime_diagnostic and Path(cached.__file__).resolve()==target),
            'unrelated cached model replay module')
    if cached is not None and Path(cached.__file__).resolve()==target:
        module=cached
    else:
        spec=importlib.util.spec_from_file_location('diagnostic',target)
        require(spec is not None and spec.loader is not None,'model replay module cannot be loaded')
        module=importlib.util.module_from_spec(spec)
        sys.modules['diagnostic']=module
        try:spec.loader.exec_module(module)
        except BaseException:
            sys.modules['diagnostic']=cached
            raise
    require(Path(module.__file__).resolve()==target,'wrong bound model replay module')
    require(sha(target)==expected,'frozen model replay changed during import')
    require(load_runtime is audit_diagnostic.load_runtime and require is audit_diagnostic.require and
            sha is audit_diagnostic.sha and write_json is audit_diagnostic.write_json,
            'audit helper globals changed during runtime module binding')
    _bound_runtime_diagnostic=module
    return dict(file=str(target),sha256=expected,audit_helper_file=str(Path(audit_diagnostic.__file__).resolve()),
                audit_helpers_preserved=True,strict_runtime_path_guard_unchanged=True)


def selected_notice(result):
    notices=result['driver']['observed_checkpoints']
    require(bool(notices),'no complete checkpoint')
    notice=max(notices,key=lambda row:row['gain'])
    require(notice['supervisor_observed_elapsed_s']<=result['driver']['hard_transform_budget_s'],
            'selected checkpoint arrived after transform deadline')
    require(Path(result['selected_checkpoint']['directory']).name==notice['directory'] and
            result['selected_checkpoint']['gain']==notice['gain'],'selected checkpoint not best recorded incumbent')
    return notice



def validate_appended_free_witnesses(p,a,s,initial_free,graph,base,step,selected,source,job,out,bound):
    """Extra-cost full-domain reconstruction and original-model authentication."""
    import free_guided as fg
    import inline_models as im
    runtime=Path(p.__file__).resolve().parent
    require(Path(fg.__file__).resolve()==runtime/'free_guided.py' and Path(im.__file__).resolve()==runtime/'inline_models.py',
            'wrong frozen free/inline audit module')
    cache={};origins={};records_by_root={};reconstructed=[]
    for c in selected:
        require('free_domain' in c,'enabled selected candidate lost free provenance')
        reference=c['free_domain']['manifest'];key=(reference['file'],reference['sha256'])
        if key not in cache:
            # Bound memory independently of the number of selected versions.
            if len(cache)>=2:cache.pop(next(iter(cache)))
            cache[key]=fg.reconstruct_free_manifest(a,source,reference,job['case']['input_sha256'],initial_free)
            reconstructed.append(dict(file=reference['file'],sha256=reference['sha256'],free_version=reference['free_version']))
            bind_files(bound,[source/'free_domains'/reference['file']])
        free,manifest=cache[key]
        fg.verify_witness_annotation(a,c,c['free_witness'],source,job['case']['input_sha256'])
        check_candidate(p,a,s,c,free)
        if c['witness_lane']<256:continue
        record=manifest['records'][c['witness_lane']-256];origin=json.loads(record['provenance_json'])
        chunk=im.artifact(source/'chunks',origin['source_chunk']);index=origin['source_candidate_index']
        candidates=json.loads((chunk/'candidates.json').read_text())
        require(type(index)is int and 0<=index<len(candidates),'free origin source index differs')
        original=candidates[index];identity=[original['root'],original['recipe'],original['out']]
        require(identity==origin['candidate_id'] and original['anytime_certificate']['candidate_index']==index and
                original['anytime_certificate']['receipts']['step']['inline_image_model']==origin['model_manifest'],
                'free witness original candidate/model binding differs')
        manifest_path=im.artifact(chunk,origin['model_manifest']['manifest_file'])
        batch=json.loads(manifest_path.read_text())
        require(batch['artifacts']['models']['sha256']==origin['models_sha256'],'free origin model-file hash differs')
        bind_files(bound,[chunk/'candidates.json',manifest_path]+[im.artifact(chunk,x['file']) for x in batch['artifacts'].values()])
        identity_key=(origin['source_chunk'],index)
        if identity_key in origins:require(origins[identity_key]==original,'conflicting free origin source rows')
        origins[identity_key]=original;records_by_root[c['root']]=(identity_key,record)
    replay_count=0
    if origins:
        # Existing full/cone collector authenticates raw bytes, reconstructs the
        # exact old CNF and independently replays every source transition/miter.
        sources=[origins[key] for key in sorted(origins)]
        target=out/'appended_free_source_replay'
        _,report=im.collect_inline_models(a,graph,base,step,sources,target,job,p.Deadline(120),
                                         dict(audit_purpose='selected appended free-witness origins'))
        replayed=json.loads((target/'replayed_models.json').read_text())
        by_source={(r['source_chunk'],r['source_proof_candidate_index']):r for r in replayed}
        require(set(by_source)==set(origins),'selected free origin model unavailable')
        for key,record in records_by_root.values():
            row=by_source[key]
            require(row['previous_inputs']==record['inputs'] and row['previous_state']==record['state'],
                    'selected free world differs from authenticated original model predecessor')
        replay_count=report['models']
    return dict(status='PASS',domain_reconstructions=reconstructed,selected_appended_witnesses=len(records_by_root),
                authenticated_distinct_source_models=replay_count,additional_solver_queries=0,
                witness_policy='complete saved free vectors reconstructed and hashed; original inline source models re-authenticated')


def validate_selected(p,product,anytime,source,result,job,input_path,out,bound):
    """Bind raw receipts and reconstruct the precise CNF/literals before reuse."""
    notice=selected_notice(result)
    checkpoint,metadata=(anytime.verify_checkpoint(source,notice,job['case']['input_sha256'],free_domain_required=True)
                         if job.get('predecessor_free') else anytime.verify_checkpoint(source,notice,job['case']['input_sha256']))
    require(checkpoint.resolve()==Path(result['selected_checkpoint']['directory']).resolve(),'checkpoint path mismatch')
    bind_files(bound,[checkpoint/'checkpoint.json']+[checkpoint/k for k in metadata['artifacts']])
    selected=json.loads((checkpoint/'selection.json').read_text())['selected']
    a=p.Aiger(input_path);s=p.Structure(a);cfg=p.Config(**job['config'])
    graph,base,step,reset=p.compile_graph(a)
    (free,_,_),_=p.signatures(graph,[base,step,reset],cfg)
    groups=defaultdict(list)
    free_validation=None
    if job.get('predecessor_free'):
        free_validation=validate_appended_free_witnesses(p,a,s,free,graph,base,step,selected,source,job,out,bound)
    for c in selected:
        if not job.get('predecessor_free'):check_candidate(p,a,s,c,free)
        groups[c['anytime_certificate']['chunk']].append(c)
    reconstructed=out/'source_proof_reconstruction';reconstructed.mkdir()
    reports=[]
    for chunk,chosen in sorted(groups.items()):
        directory=source/'chunks'/chunk
        originals=json.loads((directory/'candidates.json').read_text())
        bind_files(bound,[directory/k for k in ('candidates.json','query_literals.json','obligations.cnf')])
        g=p.Graph();g.gates=list(graph.gates);g.hash=dict(graph.hash)
        _,order=append_triples(p,g,[('free',base),('reset',reset),('step',step)],originals)
        literals=[{r['phase']:r['miter_literal'] for r in order[3*i:3*i+3]} for i in range(len(originals))]
        require(literals==json.loads((directory/'query_literals.json').read_text()),'source literal reconstruction differs')
        dest=reconstructed/(chunk+'.cnf');g.cnf(dest)
        require(sha(dest)==sha(directory/'obligations.cnf'),'source CNF reconstruction differs')
        for c in chosen:
            cert=c['anytime_certificate'];original=originals[cert['candidate_index']]
            require(original==c and cert['miter_literals']==literals[cert['candidate_index']],
                    'selected candidate differs from certificate source row')
            for receipt in cert['receipts'].values():
                bind_files(bound,[directory/receipt['queries_file'],directory/receipt['results_file']])
        reports.append(dict(chunk=chunk,cnf_sha256=sha(dest),selected=len(chosen),source_candidates=len(originals)))
    rebuilt=product.rebuild(a,selected);baseline=product.rebuild(a,[])
    require(product.write_aig(out/'original_selected_replay.aig',rebuilt)==sha(checkpoint/'product.aig'),
            'original selected replay differs')
    require(product.write_aig(out/'baseline_replay.aig',baseline)==sha(checkpoint/'replay_without_build.aig'),
            'original empty replay differs')
    require(all(r['output_is_new'] and r['output_is_live'] and r['live_created_gates']>0 for r in rebuilt['realization']),
            'original selected Build not fresh/live')
    write_json(out/'selected_builds.json',selected)
    write_json(out/'source_proof_validation.json',dict(status='PASS',selected_builds=len(selected),
        reused_verified_build_triples=len(selected),selected_free_witnesses_replayed=len(selected),chunks=reports,
        proof_reuse_scope='exact reconstructed immutable CNF and exact raw receipt assumptions; no cross-CNF reuse',
        **(dict(free_domain_validation=free_validation) if free_validation is not None else {})))
    return a,s,cfg,selected,checkpoint,len(baseline['gates']),len(rebuilt['gates'])


def enumerate_directs(p,hash_direct,a,s,cfg,selected,pools,out):
    graph,base,step,reset=p.compile_graph(a)
    (free,_,_),mask=p.signatures(graph,[base,step,reset],cfg)
    candidates=[];scope=[]
    for c in selected:
        root=c['root'];pool=pools[root]
        raw=hash_direct.collect_hash_direct(s,root,pool,cfg.max_gates)
        ordinary={0,1}|{2*n+phase for n in set(pool)|p.external_nodes(c['recipe'],c['out']) for phase in(0,1)}
        for value,witness in raw.items():
            require(p.normalize(s,root,witness['recipe'],witness['out'])==([],value),'hash Direct grammar witness differs')
        literals=sorted(ordinary|set(raw))
        scope.append(dict(root=root,pool=pool,used_divisors=sorted(p.external_nodes(c['recipe'],c['out'])),
            ordinary_literals=sorted(ordinary),grammar_zero_fresh_literals=sorted(raw),
            extra_hash_literals=sorted(set(raw)-ordinary),all_literals=literals,
            grammar_witnesses={str(v):w for v,w in raw.items()}))
        for value in literals:
            direct=dict(root=root,recipe=[],out=value,**s.cost(root,[],value),
                        scope_origin='grammar_hash_extra' if value not in ordinary else 'constants_pool_used_divisors')
            diff=free[root]^p.recipe_eval([],value,free,mask)
            if diff:
                direct['witness_lane']=(diff&-diff).bit_length()-1
                direct['free_witness']=p.witness(a,direct,free)
            candidates.append(direct)
    queries,order=append_triples(p,graph,[('free',base),('reset',reset),('step',step)],candidates)
    write_json(out/'direct_scope.json',scope)
    return graph,candidates,queries,order,scope


def checked_receipt(receipt, expected_cnf, expected_query, source, parsed_cache=None):
    require(receipt['cnf_sha256']==expected_cnf and receipt['assumptions']==expected_query,
            'reused proof CNF/assumptions mismatch')
    paths={};parsed={}
    if parsed_cache is None:parsed_cache={}
    for kind in ('queries','results'):
        name=receipt[kind+'_file']
        require(Path(name).name==name and name not in ('.','..'),'unsafe receipt path')
        path=source/name;paths[kind]=path;key=(path,kind)
        if key not in parsed_cache:
            digest=sha(path)
            if kind=='queries':data=path.read_text().splitlines()
            else:
                with path.open() as stream:data=list(csv.DictReader(stream))
            parsed_cache[key]=(digest,data)
        digest,parsed[kind]=parsed_cache[key]
        require(digest==receipt[kind+'_sha256'],'reused raw proof changed')
    lines=parsed['queries'];rows=parsed['results']
    require(len(lines)==int(lines[0])+1,'incomplete reused queries')
    row=receipt['row'];query=list(map(int,lines[row+1].split()));answer=rows[row]
    require(query==[row,len(expected_query)]+expected_query and int(answer['query'])==row,
            'reused raw row/assumptions mismatch')
    code=int(answer['result'])
    require(code in (-1,0,1) and receipt['result']=={-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[code],
            'reused raw status mismatch')
    return code,paths


def reused_direct_answers(broker,candidates,queries,order,reuse,out):
    previous=json.loads((reuse/'candidates.json').read_text())
    require(json.loads((reuse/'query_order.json').read_text())==order and len(previous)==len(candidates),
            'reused query-to-candidate identity mismatch')
    require(sha(reuse/'obligations.cnf')==broker.fingerprint,'reused immutable CNF differs')
    answers=[];receipts=[];copied={};pending=[];parsed_cache={}
    for i,(c,old) in enumerate(zip(candidates,previous)):
        old_base={k:v for k,v in old.items() if k not in ('proof','proof_receipts','sequentially_proved')}
        require(c==old_base,'reused candidate/cost/witness identity mismatch')
        for offset,phase in enumerate(('free','reset','step')):
            receipt=old['proof_receipts'][phase];index=3*i+offset
            code,paths=checked_receipt(receipt,broker.fingerprint,queries[index],reuse,parsed_cache)
            answers.append(code);receipts.append(dict(receipt,reused_from_audit=True))
            for path in paths.values():copied[path.name]=path
            if code==0:pending.append(index)
    for name,path in copied.items():shutil.copyfile(path,out/name)
    if pending:
        fresh,raw=broker.solve([queries[i]for i in pending],'unknown_recheck')
        for index,code,receipt in zip(pending,fresh,raw):answers[index]=code;receipts[index]=receipt
    previous_report=json.loads((reuse/'report.json').read_text())
    write_json(out/'reused_report.json',previous_report)
    return answers,receipts,len(answers)-len(pending)


def prove_directs(p,anytime,graph,candidates,queries,order,solver,seconds,out,solver_identity,reuse=None):
    out.mkdir()
    broker=anytime.FrozenQueries(graph,out,solver,p.Deadline(seconds),solver_identity)
    reused=0
    if reuse is None:answers,receipts=broker.solve(queries,'direct_free_reset_image')
    else:answers,receipts,reused=reused_direct_answers(broker,candidates,queries,order,reuse,out)
    require(len(answers)==3*len(candidates),'incomplete direct proofs')
    valid=[]
    for i,c in enumerate(candidates):
        triple=answers[3*i:3*i+3]
        c['proof']=dict(zip(('free','reset','step'),({-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[v] for v in triple)))
        c['proof_receipts']=dict(zip(('free','reset','step'),receipts[3*i:3*i+3]))
        c['sequentially_proved']=triple[1:]==[-1,-1]
        require(not(triple[0]==-1 and 'free_witness'in c),'free Direct witness contradicts proof')
        if c['sequentially_proved'] and c['conservative_gain']>0:valid.append(c)
    write_json(out/'query_order.json',order);write_json(out/'candidates.json',candidates)
    report=broker.report();report.update(logical_requested_queries=len(queries),reused_conclusive_source_queries=reused,
        reuse_source=str(reuse)if reuse else None);write_json(out/'report.json',report)
    return valid,report


def existing_dsec_cache(product,result,source,checkpoint,abc_hash,input_hash,bound):
    cache={}
    for key,artifact,logname in [('baseline_dsec','replay_without_build.aig','baseline_dsec.log'),
                                  ('independent_dsec','product.aig','dsec.log')]:
        r=result['product'][key]
        require(result['product']['input_sha256']==input_hash and r['abc_sha256']==abc_hash,'original DSEC identity mismatch')
        path=source/logname
        require(sha(path)==r['log_sha256'],'original DSEC log changed')
        bind_files(bound,[path])
        status=product.dsec_answer(dict(status='exit' if r['exit_code']==0 else 'error'),path.read_text()).upper()
        require(status==r['status']=='PASS','original DSEC was not PASS')
        expected_command=f"dsec {Path(json.loads((source/'job.json').read_text())['case']['input']).resolve()} {(checkpoint/artifact).resolve()}"
        require(r['command']==expected_command,'original DSEC command identity mismatch')
        digest=sha(checkpoint/artifact)
        require(digest==result['product']['replay_without_build_sha256' if key=='baseline_dsec' else 'product_sha256'],
                'original DSEC product hash mismatch')
        cache[(input_hash,digest,abc_hash)]=dict(**r,reused_exact_graph_dsec=True,
            reused_log=str(path),charged_new_wall_s=0.0)
    return cache


def seed_reused_dsec_cache(product,reuse,input_hash,abc_hash,cache,bound):
    previous=json.loads((reuse/'result.json').read_text())
    require(previous['input_sha256']==input_hash,'reused DSEC input identity mismatch')
    for name,r in previous['arms'].items():
        certificate=r['dsec'];artifact=reuse/name/'product.aig';digest=sha(artifact)
        require(digest==r['sha256'] and certificate['abc_sha256']==abc_hash,'reused DSEC artifact/ABC identity mismatch')
        log=Path(certificate['reused_log']);require(sha(log)==certificate['log_sha256'],'reused DSEC log changed')
        command=certificate['command'].split()
        require(len(command)==3 and command[0]=='dsec' and sha(command[1])==input_hash and sha(command[2])==digest,
                'reused DSEC command graph identity mismatch')
        status=product.dsec_answer(dict(status='exit' if certificate['exit_code']==0 else 'error'),log.read_text()).upper()
        if status==certificate['status']=='PASS':
            cache[(input_hash,digest,abc_hash)]=dict(certificate,reused_exact_graph_dsec=True,charged_new_wall_s=0.0)
        bind_files(bound,[artifact,log,Path(command[1]),Path(command[2]),reuse/'result.json'])


def emit_product(product,a,selected,name,out,input_path,abc,seconds,cache,input_hash,abc_hash):
    directory=out/name;directory.mkdir();rebuilt=product.rebuild(a,selected)
    digest=product.write_aig(directory/'product.aig',rebuilt)
    write_json(directory/'selection.json',dict(selected=selected,realization=rebuilt['realization']))
    key=(input_hash,digest,abc_hash)
    if key in cache:certificate=dict(cache[key],reused_exact_graph_dsec=True,charged_new_wall_s=0.0)
    else:
        certificate=product.dsec(abc,input_path,directory/'product.aig',directory,seconds,'dsec')
        certificate.update(reused_exact_graph_dsec=False,charged_new_wall_s=certificate['wall_s'],reused_log=str(directory/'dsec.log'))
        if certificate['status']=='PASS':cache[key]=copy.deepcopy(certificate)
    result=dict(and_count=len(rebuilt['gates']),sha256=digest,selected=len(selected),dsec=certificate)
    write_json(directory/'result.json',result)
    return result,rebuilt


def case_audit(p,product,anytime,hash_direct,run,name,out,args,plan):
    start=time.monotonic();out.mkdir();source=run/name
    job=json.loads((source/'job.json').read_text());result=json.loads((source/'result.json').read_text())
    require(job['source_hashes']==plan['runtime_source_hashes'],'job source differs from plan')
    require(result['status'] in ('COMPLETE','BUDGET_EXHAUSTED'),'invalid original transform status')
    bound={};bind_files(bound,[source/'job.json',source/'result.json',source/'root_search.jsonl',run/'plan.json'])
    original=Path(job['case']['input']);input_hash=job['case']['input_sha256']
    require(sha(original)==input_hash,'original input changed');bind_files(bound,[original])
    loaded=original.parents[2]/job['case']['loaded_path']
    require(sha(loaded)==job['case']['loaded_sha256'] and p.Aiger(loaded).na==job['case']['loaded_AND'],'loaded denominator mismatch')
    bind_files(bound,[loaded]);shutil.copyfile(original,out/'input.aig');input_path=out/'input.aig'
    require(sha(input_path)==input_hash,'copied input identity mismatch');bind_files(bound,[input_path])
    a,s,cfg,selected,checkpoint,baseline_and,original_and=validate_selected(p,product,anytime,source,result,job,input_path,out,bound)
    source_s=time.monotonic()-start
    roots=[json.loads(line) for line in (source/'root_search.jsonl').read_text().splitlines()]
    require(len({r['root'] for r in roots})==len(roots),'duplicate saved root pool')
    pools={r['root']:r['pool'] for r in roots}
    t=time.monotonic();graph,direct,queries,order,scope=enumerate_directs(p,hash_direct,a,s,cfg,selected,pools,out)
    enumeration_s=time.monotonic()-t
    t=time.monotonic();valid,proof_stats=prove_directs(p,anytime,graph,direct,queries,order,args.solver,args.proof_seconds,
                                                  out/'direct_proofs',args.solver_identity,
                                                  args.reuse_audit/name/'direct_proofs'if args.reuse_audit else None)
    proof_s=time.monotonic()-t
    t=time.monotonic();comparisons=[]
    for c in selected:
        same_root=[d for d in valid if d['root']==c['root']]
        build_single=baseline_and-len(product.rebuild(a,[c])['gates'])
        alternatives=[]
        for d in same_root:
            single=baseline_and-len(product.rebuild(a,[d])['gates'])
            same_other=[d if b['root']==c['root'] else b for b in selected]
            alternatives.append(dict(out=d['out'],scope_origin=d['scope_origin'],conservative_gain=d['conservative_gain'],
                retained_mffc_nodes=d['retained_mffc_nodes'],exact_single_direct_gain=single,
                exact_gain_with_other_original_selected_builds=baseline_and-len(product.rebuild(a,same_other)['gates']),
                proof=d['proof'],free_witness_replayed='free_witness'in d))
        best=max((d['exact_single_direct_gain'] for d in alternatives),default=None)
        comparisons.append(dict(root=c['root'],build_exact_single_gain=build_single,build_conservative_gain=c['conservative_gain'],
            direct_alternatives=alternatives,best_direct_single_gain=best,
            direct_weakly_dominates_single_replacement=best is not None and best>=build_single))
    write_json(out/'per_root_comparison.json',comparisons)
    single_root_s=time.monotonic()-t
    cache=existing_dsec_cache(product,result,source,checkpoint,plan['abc_sha256'],input_hash,bound)
    if args.reuse_audit:seed_reused_dsec_cache(product,args.reuse_audit/name,input_hash,plan['abc_sha256'],cache,bound)
    t=time.monotonic();arms={};sets={}
    for label,candidates in [('direct_only',valid),('mixed',valid+selected)]:
        chosen,rejected=product.select(s,candidates)
        arms[label],rebuilt=emit_product(product,a,chosen,label,out,input_path,args.abc,args.dsec_seconds,cache,input_hash,plan['abc_sha256'])
        arms[label].update(exact_gain=baseline_and-arms[label]['and_count'],rejected=rejected)
        write_json(out/label/'result.json',arms[label]);sets[label]=(chosen,rebuilt)
    mixed,rebuild=sets['mixed'];realizations={r['root']:r for r in rebuild['realization']}
    actual=[c for c in mixed if c['recipe'] and realizations[c['root']]['output_is_new'] and
            realizations[c['root']]['output_is_live'] and realizations[c['root']]['live_created_gates']>0]
    actual_roots={c['root']for c in actual};without=[c for c in mixed if c['root']not in actual_roots]
    arms['same_mixed_set_without_build'],_=emit_product(product,a,without,'same_mixed_set_without_build',out,input_path,args.abc,
        args.dsec_seconds,cache,input_hash,plan['abc_sha256'])
    build_marginal=arms['same_mixed_set_without_build']['and_count']-arms['mixed']['and_count']
    rebuild_dsec_s=time.monotonic()-t
    require(sha(input_path)==input_hash,'copied input changed during audit')
    verify_bound(bound);write_json(out/'source_manifest.json',bound)
    total=time.monotonic()-start;dsec_s=sum(r['dsec']['charged_new_wall_s'] for r in arms.values())
    final=dict(case=name,status='ATTRIBUTION_AUDIT_COMPLETE',original_transform_status=result['status'],
        original_search_complete=result['search_complete'],selected_checkpoint=str(checkpoint),input_sha256=input_hash,
        loaded_and=job['case']['loaded_AND'],input_and=a.na,baseline_and=baseline_and,
        original_selected_builds=len(selected),raw_build_only_gain=baseline_and-original_and,
        selected_root_direct_candidates=len(direct),extra_hash_direct_literals=sum(len(r['extra_hash_literals']) for r in scope),
        proved_positive_directs=len(valid),proved_extra_hash_directs=sum(d['scope_origin']=='grammar_hash_extra' for d in valid),
        roots_with_proved_directs=len({d['root']for d in valid}),
        roots_direct_weakly_dominates_single_replacement=sum(r['direct_weakly_dominates_single_replacement'] for r in comparisons),
        direct_proof=proof_stats,arms=arms,mixed_actual_fresh_builds=len(actual),
        mixed_syntactic_builds_demoted_to_direct=sum(bool(c['recipe']) for c in mixed)-len(actual),
        exact_same_mixed_selected_set_build_marginal=build_marginal,
        validated_conditional_fresh_build_marginal=(build_marginal if all(r['dsec']['status']=='PASS'for r in arms.values())else None),
        additional_wall_s=total,additional_non_dsec_wall_s=total-dsec_s,
        timing=dict(source_verification_s=source_s,direct_enumeration_s=enumeration_s,direct_proof_s=proof_s,
                    single_root_cleanup_s=single_root_s,rebuild_and_dsec_s=rebuild_dsec_s,new_dsec_s=dsec_s),
        new_dsec_calls=sum(not r['dsec']['reused_exact_graph_dsec'] for r in arms.values()),
        reused_exact_graph_dsec=sum(r['dsec']['reused_exact_graph_dsec'] for r in arms.values()),
        source_evidence_unchanged=True,same_transform_budget_claim=False,native_novelty='NOT_CHECKED',
        scope='original selected roots; constants, both phases of saved pools and used divisors, plus zero-fresh exact same 1/2-AND grammar outputs; not global Direct exhaustion')
    write_json(out/'result.json',final)
    print(json.dumps({k:final[k]for k in ('case','raw_build_only_gain','validated_conditional_fresh_build_marginal',
        'mixed_actual_fresh_builds','proved_positive_directs','proved_extra_hash_directs','additional_wall_s','new_dsec_calls')}),flush=True)
    return final


def aggregate(rows):
    valid=[r for r in rows if r.get('validated_conditional_fresh_build_marginal')is not None]
    gain=lambda r:r['validated_conditional_fresh_build_marginal']
    def stats(rs):
        return dict(cases=len(rs),gain=sum(map(gain,rs)),equal_case_percent=100*sum(gain(r)/r['loaded_and']for r in rs)/len(rs)if rs else None,
                    weighted_percent=100*sum(map(gain,rs))/sum(r['loaded_and']for r in rs)if rs else None)
    largest=max(valid,key=gain,default=None)
    return dict(validated=stats(valid),excluding_largest_contributor=stats([r for r in valid if r is not largest]),
        largest_contributor=largest['case']if largest else None,positive_cases=[r['case']for r in valid if gain(r)>0],
        by_loaded_size={name:stats([r for r in valid if lo<=r['loaded_and']<hi])for name,lo,hi in
            [('lt1k',0,1000),('1k_to_10k',1000,10000),('10k_to_100k',10000,100000),('ge100k',100000,float('inf'))]},
        original_search_completion={r['case']:r.get('original_search_complete')for r in rows},
        additional_audit_wall_s=sum(r.get('additional_wall_s',0)for r in rows),
        attribution='conditional fresh-Build marginal after bounded selected-root matched-grammar Direct sensitivity; additional audit cost',
        native_novelty='NOT_CHECKED',global_direct_exhaustion=False)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);ap.add_argument('--solver',type=Path,required=True);ap.add_argument('--abc',type=Path,required=True)
    ap.add_argument('--reuse-audit',type=Path);ap.add_argument('--case',action='append');ap.add_argument('--proof-seconds',type=float,default=120);ap.add_argument('--dsec-seconds',type=float,default=120)
    args=ap.parse_args();run=args.run.resolve();args.out=args.out.resolve();args.solver=args.solver.resolve();args.abc=args.abc.resolve()
    validate_output(args.out,run,run);require(args.proof_seconds>0 and args.dsec_seconds>0,'positive budgets required')
    plan=json.loads((run/'plan.json').read_text());require(json.loads((run/'source_integrity.json').read_text())['status']=='PASS','source integrity not PASS')
    bound={str(run/'source'/name):digest for name,digest in plan['runtime_source_hashes'].items()}
    bind_files(bound,[run/'plan.json',run/'source_integrity.json',Path(__file__),HERE/'diagnostic.py',HERE/'audit_products.py'])
    require(sha(args.solver)==plan['solver_sha256'] and sha(args.abc)==plan['abc_sha256'],'solver/ABC mismatch')
    bound[str(args.solver)]=plan['solver_sha256'];bound[str(args.abc)]=plan['abc_sha256']
    verify_bound(bound)
    replay_binding=(bind_runtime_model_replay(run/'source',plan['runtime_source_hashes'],bound)
                    if plan.get('predecessor_free') else None)
    p=load_runtime(run/'source');product=importlib.import_module('product');anytime=importlib.import_module('anytime')
    args.solver_identity,_=anytime.bind_executable(args.solver,plan['solver_sha256'])
    if args.reuse_audit:
        args.reuse_audit=args.reuse_audit.resolve();validate_output(args.out,args.reuse_audit,args.reuse_audit)
        prior=json.loads((args.reuse_audit/'plan.json').read_text())
        require(prior['source_run']==str(run) and json.loads((args.reuse_audit/'integrity.json').read_text())['status']=='PASS',
                'reused audit source/integrity differs')
        require(prior['source_and_tool_sha256'][str(args.solver)]==plan['solver_sha256'] and
                prior['source_and_tool_sha256'][str(args.abc)]==plan['abc_sha256'],'reused executables differ')
        bind_files(bound,[path for path in args.reuse_audit.rglob('*')if path.is_file()])
    require(Path(product.__file__).resolve()==run/'source/nonlinear_divisors/product.py' and
            Path(anytime.__file__).resolve()==run/'source/nonlinear_divisors/anytime.py','wrong frozen module')
    helper=HERE.parent/'nonlinear_divisors/hash_direct_audit.py';bind_files(bound,[helper]);verify_bound(bound)
    spec=importlib.util.spec_from_file_location('bounded_hash_direct',helper);hash_direct=importlib.util.module_from_spec(spec);spec.loader.exec_module(hash_direct)
    args.out.mkdir();(args.out/'source').mkdir()
    for path in (Path(__file__),HERE/'diagnostic.py',HERE/'audit_products.py',helper):shutil.copyfile(path,args.out/'source'/path.name)
    selected=args.case or [Path(name).stem for name in plan['cases']]
    require(set(selected)<={Path(name).stem for name in plan['cases']},'unknown case')
    write_json(args.out/'plan.json',dict(source_run=str(run),cases=selected,source_and_tool_sha256=bound,
        query_policy='all direct free/reset/image; conclusive memoization on same immutable CNF and assumptions only',
        original_evidence_read_only=True,additional_audit_cost=True,
        **(dict(model_replay_module_binding=replay_binding) if replay_binding else {})))
    rows=[]
    for name in selected:
        try:r=case_audit(p,product,anytime,hash_direct,run,name,args.out/name,args,plan)
        except Exception as error:
            r=dict(case=name,status='ERROR',error=repr(error),validated_conditional_fresh_build_marginal=None)
            (args.out/name).mkdir(exist_ok=True);(args.out/name/'error.log').write_text(traceback.format_exc())
            write_json(args.out/name/'result.json',r);print(json.dumps(r),flush=True)
        rows.append(r);write_json(args.out/'results.json',rows);write_json(args.out/'summary.json',aggregate(rows))
    require(anytime.file_identity(args.solver)==args.solver_identity,'initial solver identity changed')
    verify_bound(bound);write_json(args.out/'integrity.json',dict(status='PASS',source_and_helpers_unchanged=True))
    return 1 if any(r['status']=='ERROR'for r in rows)else 0


if __name__=='__main__':raise SystemExit(main())
