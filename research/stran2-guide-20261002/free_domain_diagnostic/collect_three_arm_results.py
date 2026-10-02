#!/usr/bin/env python3
"""Read-only compact extraction from the completed, immutable three-arm run."""
import argparse
import csv
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path

ARMS=('inline_free_off','predecessor_cache_off','predecessor_cache_on')
def read(path):return json.loads(Path(path).read_text())
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def bind(path):
    path=Path(path).resolve()
    return dict(path=str(path),sha256=sha(path),bytes=path.stat().st_size)
def write(path,value):Path(path).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def compact_product(value):
    return {k:v for k,v in value.items()if k not in('rejected','selected_ids')}
def collect(root,out):
    root=root.resolve();out=out.resolve()
    assert not out.is_relative_to(root),'never write into frozen run'
    assert not out.exists(),'new packet directory required'
    out.mkdir(parents=True)
    core={name:bind(root/name)for name in('plan.json','approval_gate.json','execution.json','summary.json','ledger.json','controller-first.log')}
    plan=read(root/'plan.json');execution=read(root/'execution.json');summary=read(root/'summary.json');ledger=read(root/'ledger.json')
    assert execution['status']=='FINISHED'and execution['source_and_tools_unchanged']
    assert len(ledger)==len(plan['ordered_jobs'])==18
    assert execution['plan_sha256']==core['plan.json']['sha256']
    assert [(r['case'],r['arm'])for r in ledger]==[(j['case'],j['arm'])for j in plan['ordered_jobs']]
    arms=[];csv_rows=[]
    for record in ledger:
        case=record['case'];arm=record['arm'];stem=Path(case).stem
        a=record.get('analysis',{});result=a.get('result',{});guidance=a.get('guidance',{});funnel=a.get('positive_funnel',{})
        direct=record.get('direct_result',{});global_result=record.get('global_result',{})
        run_dir=root/'runs'/stem/arm;case_dir=run_dir/stem;direct_dir=root/'audits'/stem/arm/'direct'/stem;global_dir=direct_dir.parent.parent/'global'/stem
        checkpoint=result.get('selected_checkpoint',{});checkpoint_dir=Path(checkpoint['directory'])if checkpoint else None
        artifacts=[]
        for p in (run_dir/'plan.json',run_dir/'source_integrity.json',case_dir/'job.json',case_dir/'result.json',
                  direct_dir/'source_manifest.json',direct_dir/'source_proof_validation.json',direct_dir/'result.json',
                  direct_dir/'direct_scope.json',direct_dir/'direct_proofs/report.json',global_dir/'source_manifest.json',global_dir/'result.json'):
            if p.exists():artifacts.append(bind(p))
        if checkpoint_dir:
            for name in ('checkpoint.json','selection.json','product_result.json','product.aig','replay_without_build.aig'):
                artifacts.append(bind(checkpoint_dir/name))
        # Small exact graph/log/classification bindings only, never duplicate raw proof ledgers.
        for folder in (direct_dir,global_dir):
            if folder.exists():
                for pattern in ('*.aig','*dsec*.log','classification.json','selected_sets.json','selection.json'):
                    for p in sorted(folder.rglob(pattern)):artifacts.append(bind(p))
        for name in ('baseline_dsec.log','dsec.log'):
            if(case_dir/name).exists():artifacts.append(bind(case_dir/name))
        artifacts=list({r['path']:r for r in artifacts}.values())
        driver=record.get('driver',{});product=result.get('product',{})
        timing=dict(transform_process_wall_s=a.get('transform_wall_s'),transform_hard_cap_s=a.get('transform_hard_cap_s'),
            driver_wall_including_original_dsec_s=driver.get('wall_s'),original_product_dsec_s=record.get('baseline_product_dsec_wall_s'),
            fresh_direct_driver_s=record.get('direct_audit_driver',{}).get('wall_s'),
            fresh_global_driver_s=record.get('global_audit_driver',{}).get('wall_s'),
            direct_additional_non_dsec_s=direct.get('additional_non_dsec_wall_s'),direct_timing=direct.get('timing'),
            global_additional_s=global_result.get('additional_wall_s'),global_new_dsec_s=global_result.get('new_dsec_wall_s'),
            fresh_audit_dsec_calls=direct.get('new_dsec_calls',0)+global_result.get('new_dsec_calls',0),
            original_dsec_calls=2 if product else 0,observer_work_s=driver.get('sampling_work_wall_s'))
        memory={k:driver.get(k)for k in ('transform_rss_status','sampled_transform_tree_peak_rss_kib',
            'matched_worker_complete_samples','partial_samples_skipped','worker_identity_mismatch_samples',
            'worker_process_bindings','worker_peak_processes','sampling_interval_s','memory_note')}
        row=dict(case=case,arm=arm,order=record['order'],validation_status=record['status'],error=record.get('error'),
            transform_status=a.get('status'),search_complete=a.get('search_complete'),
            genuine_build_and=global_result.get('global_hash_corrected_conditional_build_marginal'),
            raw_build_only_gain=direct.get('raw_build_only_gain'),loaded_and=direct.get('loaded_and'),timing=timing,memory=memory,
            checkpoint=dict(directory=str(checkpoint_dir)if checkpoint_dir else None,
                on_time_notice_elapsed_s=checkpoint.get('supervisor_observed_elapsed_s'),
                admitted_proof_chunk_prefix=a.get('admitted_proof_chunk_prefix'),candidate_count_scope=a.get('candidate_count_scope')),
            counts=dict(retained=len(a.get('candidate_ids',[])),qualified=len(a.get('qualified_ids',[])),selected=len(a.get('selected_ids',[])),
                appended_witness_retained=len(a.get('appended_witness_ids',[])),appended_witness_qualified=len(a.get('appended_witness_qualified_ids',[]))),
            positive_funnel=funnel,funnel_evidence_source=a.get('funnel_evidence_source'),
            guidance_evidence_source=a.get('guidance_evidence_source'),guidance=guidance,
            free_manifest_versions=a.get('free_manifest_files',[]),selected_ids=a.get('selected_ids',[]),
            appended_witness_qualified_ids=a.get('appended_witness_qualified_ids',[]),
            original_product=product,direct_products={k:compact_product(v)for k,v in direct.get('arms',{}).items()},
            global_products=global_result.get('products'),fresh_direct_proof=direct.get('direct_proof'),disk=record.get('disk'),artifacts=artifacts)
        arms.append(row)
        csv_rows.append(dict(case=case,arm=arm,validation_status=row['validation_status'],transform_status=row['transform_status'],
            genuine_build_and=row['genuine_build_and'],transform_s=timing['transform_process_wall_s'],
            direct_audit_s=timing['fresh_direct_driver_s'],global_audit_s=timing['fresh_global_driver_s'],
            original_dsec_s=timing['original_product_dsec_s'],new_audit_dsec_calls=timing['fresh_audit_dsec_calls'],
            sampled_rss_kib=memory['sampled_transform_tree_peak_rss_kib'],rss_status=memory['transform_rss_status'],
            searched_roots=funnel.get('searched_roots'),retained=row['counts']['retained'],qualified=row['counts']['qualified'],
            selected=row['counts']['selected'],appended_qualified=row['counts']['appended_witness_qualified']))
    totals={arm:sum(r['genuine_build_and']for r in arms if r['arm']==arm)if all(type(r['genuine_build_and'])is int for r in arms if r['arm']==arm)else None for arm in ARMS}
    packet=dict(schema=1,status='WORKER_TERMINAL_PASS_AWAITING_INDEPENDENT_REVIEW',run=str(root),immutable_core=core,
        collector=bind(__file__),plan_scope={k:plan[k]for k in('runtime_commit','source_head','config','arms','workers','conflicts_per_query',
            'global_added_free_cap','free_only_revisit_cap_per_chunk','inline_cone_check','order_policy','validator','audit_policy','disk_policy','environment_recovery')},
        exact_source_input_bindings=plan['source_freeze_sha256'],exact_external_bindings=plan['external_bindings'],
        total_genuine_build_and=totals,coverage=dict(validated_arms=execution['validated'],fixed_arms=18,
            complete_search_arms=sum(r['search_complete']is True for r in arms),
            validated_timeout_incumbents=sum(r['transform_status']=='BUDGET_EXHAUSTED'and r['validation_status']=='VALIDATED'for r in arms),
            sampled_rss_observed=sum(r['memory']['transform_rss_status']=='OBSERVED_SAMPLED'for r in arms)),
        timing_totals=dict(start_utc=datetime.fromtimestamp(execution['started_unix'],timezone.utc).isoformat(),
            finish_utc=datetime.fromtimestamp(execution['finished_unix'],timezone.utc).isoformat(),
            wrapper_wall_s=execution['finished_unix']-execution['started_unix'],
            transform_process_s=sum(r['timing']['transform_process_wall_s']or 0 for r in arms),
            original_product_dsec_s=sum(r['timing']['original_product_dsec_s']or 0 for r in arms),
            direct_audit_driver_s=sum(r['timing']['fresh_direct_driver_s']or 0 for r in arms),
            global_audit_driver_s=sum(r['timing']['fresh_global_driver_s']or 0 for r in arms),
            new_audit_dsec_s=sum((r['timing']['direct_timing']or{}).get('new_dsec_s',0)+(r['timing']['global_new_dsec_s']or 0)for r in arms),
            new_audit_dsec_calls=sum(r['timing']['fresh_audit_dsec_calls']for r in arms),original_dsec_calls=sum(r['timing']['original_dsec_calls']for r in arms),
            transform_observer_work_s=sum(r['timing']['observer_work_s']or 0 for r in arms),
            note='DSEC subcomponents are included in the corresponding driver times; do not add them twice.'),
        paired_contrasts=summary['contrasts'],case_contrasts=summary['cases'],arms=arms,
        inference_boundary='One preregistered rotated observation per case/arm under120s. Cache recovers some uncached-free losses; cached predecessor-free remains below current inline baseline. No broad gain, native novelty, or cross-recovery historical timing claim.',
        memory_limitations='100ms requested sampling plus observer overhead; sums shared pages; short-lived peaks may be missed. Cached b20 remains null due to multiple worker identities. This is not exact peak memory.',
        timeout_boundary='Only on-time admitted checkpoints count as products. Discovery/funnel progress may be later than the admitted proof prefix; success-final cache reports are absent after timeout.',
        scope_closed=True,no_further_cache_tuning_or_expanded_cohort=True,independent_reviews=[])
    for name,row in core.items():assert sha(root/name)==row['sha256'],'frozen core changed during extraction'
    write(out/'packet.worker.json',packet)
    with(out/'arms.csv').open('w')as f:
        writer=csv.DictWriter(f,fieldnames=list(csv_rows[0]));writer.writeheader();writer.writerows(csv_rows)
    write(out/'index.worker.json',dict(status=packet['status'],files=[bind(out/'packet.worker.json'),bind(out/'arms.csv')]))
    return dict(totals=totals,coverage=packet['coverage'],timing=packet['timing_totals'],packet=bind(out/'packet.worker.json'))
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',type=Path,required=True);parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();print(json.dumps(collect(args.run,args.out),indent=2))
