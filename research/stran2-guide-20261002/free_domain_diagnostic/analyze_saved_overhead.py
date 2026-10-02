#!/usr/bin/env python3
"""Bounded metadata-only accounting; no solver, runtime replay, or timing rerun."""
import argparse
from collections import Counter,defaultdict
import hashlib
import json
from pathlib import Path
import time

class Reader:
    def __init__(self):self.start=time.monotonic();self.bytes=0;self.bound={}
    def raw(self,path):
        path=Path(path)
        if time.monotonic()-self.start>120:raise TimeoutError('120s metadata accounting cap')
        size=path.stat().st_size
        if size>64*1024**2 or self.bytes+size>512*1024**2:raise ValueError('metadata byte cap')
        data=path.read_bytes();self.bytes+=len(data);self.bound[str(path)]=hashlib.sha256(data).hexdigest();return data
    def json(self,path):return json.loads(self.raw(path))
    def rows(self,path):return [json.loads(line) for line in self.raw(path).splitlines() if line]

def account(case,analysis,chunk_size,reader):
    roots=reader.rows(case/'root_search.jsonl');root_group={r['root']:i//chunk_size for i,r in enumerate(roots)}
    manifests={};sizes={};canonical_sizes={}
    for path in sorted((case/'free_domains').glob('version_*.json')):
        data=reader.raw(path);row=json.loads(data);v=row['free_version'];manifests[v]=row;sizes[v]=len(data)
        canonical_sizes[v]=len(json.dumps(row,sort_keys=True,separators=(',',':'),allow_nan=False).encode())
    assert sorted(manifests)==list(range(len(manifests)))
    chunks={};proof_checks=Counter()
    for path in sorted((case/'chunks').glob('chunk_*/candidates.unproved.json')):
        cs=reader.json(path);chunks[path.parent.name]=cs
        for c in cs:proof_checks[c['free_domain']['manifest']['free_version']]+=1
    rounds=[];unknown_rounds=[]
    for directory in sorted((case/'image_guidance').glob('round_*')):
        if not (directory/'provenance.json').exists():
            unknown_rounds.append(dict(round=directory.name,reason='no complete provenance'));continue
        provenance=reader.json(directory/'provenance.json');source_roots=[]
        for ref in provenance['query_sources']:
            source_roots.append(chunks[ref['chunk']][ref['candidate_index']]['root'])
        source_roots.extend(r['candidate_id'][0]for r in provenance['model_unavailable'])
        groups={root_group[root]for root in source_roots}
        assert len(groups)==1,(directory,groups)
        admission=reader.json(directory/'free_admission.json')if (directory/'free_admission.json').exists()else None
        refinement=reader.json(directory/'refinement.json')if (directory/'refinement.json').exists()else None
        rounds.append(dict(round=directory.name,group=groups.pop(),admission=admission,refinement=refinement))
    assert [r['group']for r in rounds]==sorted(r['group']for r in rounds)
    by_group=defaultdict(list)
    for row in rounds:by_group[row['group']].append(row)
    repeats=Counter();empty=Counter();root_versions={};version=0;teacher=0
    for group in range((len(roots)+chunk_size-1)//chunk_size):
        group_roots=roots[group*chunk_size:(group+1)*chunk_size]
        assert all(r['teacher_version']==teacher for r in group_roots)
        for row in group_roots:
            repeats[version]+=1;empty[version]+=int(row['candidates']==0);root_versions[row['root']]=version
        for row in by_group[group]:
            admission,refinement=row['admission'],row['refinement']
            if admission:
                assert admission['before_version']==version
                version=admission['after_version']
                assert version in manifests
            if refinement:
                assert refinement['teacher_version_before']==teacher
                teacher=refinement['teacher_version_after']
                assert refinement['free_domain']['free_version']==version
                if refinement['discovery_executed_roots']+refinement['discovery_skipped_unchanged_projection_roots']:
                    repeats[version]+=1;empty[version]+=int(refinement['new_candidates']==0)
    complete=analysis['status']=='COMPLETE'
    if complete:assert not unknown_rounds and all(r['refinement']is not None for r in rounds)
    per_version=[dict(version=v,world_records=len(manifests[v]['records']),manifest_file_bytes=sizes[v],
        canonical_payload_bytes=canonical_sizes[v],completed_repeat_persist_calls=repeats[v],
        repeat_calls_with_empty_candidate_batch=empty[v],completed_preproof_manifest_checks=proof_checks[v])for v in manifests]
    refinements=[r['refinement']for r in rounds if r['refinement']is not None]
    # Every logged initial root is emitted after annotate/persist. Each complete
    # searching refinement likewise records after batch annotation. Each saved
    # version witnesses its one creation. Timeout may hide one in-flight call.
    return dict(persist_accounting_scope='exact for COMPLETE, completed-work lower bound for timed-out runs',
        completed_root_annotations=len(roots),completed_refinement_annotations=sum(
            bool(r['discovery_executed_roots']+r['discovery_skipped_unchanged_projection_roots'])for r in refinements),
        manifest_creations_observed=len(manifests),known_persist_calls=len(manifests)+sum(repeats.values()),
        possible_additional_inflight_persist_calls=0 if complete else 1,
        completed_repeat_persist_calls=sum(repeats.values()),empty_batch_repeat_persist_calls=sum(empty.values()),
        repeat_manifest_hash_and_text_read_bytes=2*sum(repeats[v]*sizes[v]for v in manifests),
        repeat_canonical_serialized_bytes=sum(repeats[v]*canonical_sizes[v]for v in manifests),
        repeat_json_parsed_bytes=sum(repeats[v]*(sizes[v]+canonical_sizes[v])for v in manifests),
        record_asdict_materializations=sum((1+repeats[v])*len(manifests[v]['records'])for v in manifests),
        completed_preproof_manifest_checks=sum(proof_checks.values()),
        preproof_manifest_hash_and_text_read_bytes=2*sum(proof_checks[v]*sizes[v]for v in manifests),
        preproof_json_parsed_bytes=sum(proof_checks[v]*sizes[v]for v in manifests),
        successful_creation_write_bytes=sum(sizes.values()),
        original_model_collector_wall_s_completed_rounds=sum(r['model_report']['wall_s']for r in refinements),
        completed_rounds=len(refinements),incomplete_rounds=[r['round']for r in rounds if r['refinement']is None]+unknown_rounds,
        per_version=per_version,
        costs_not_timed_separately=['persist serialization/hash/parse','dual projection construction/validation',
            'candidate full-AIG annotation replay','preproof full-AIG verification','second admission raw-receipt authentication'])

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--pilot',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
    assert not args.out.exists();reader=Reader();plan=reader.json(args.pilot/'plan.json')
    assert reader.json(args.pilot/'execution.json')['status']=='FINISHED'
    for name in ('nonlinear_divisors/free_guided.py','nonlinear_divisors/image_guided.py',
                 'nonlinear_divisors/anytime.py','free_domain_diagnostic/free_state.py'):
        path=args.pilot/'source'/name;assert hashlib.sha256(reader.raw(path)).hexdigest()==plan['source_freeze_sha256']['source/'+name]
    rows=[]
    for record in plan['ordered_jobs']:
        stem=Path(record['case']).stem;case=Path(record['directory'])/stem
        result=reader.json(case/'result.json');terminal=result.get('transform')or {};progress=result.get('last_completed_chunk')or {}
        analysis=dict(status=result['status'],transform_wall_s=result['driver']['transform_process_wall_s'],
                      positive_funnel=terminal.get('metrics')or progress.get('metrics')or {})
        timing=terminal.get('timing')or progress.get('timing')or {};guidance=terminal.get('image_guidance')or progress.get('image_guidance')or {}
        elapsed=terminal.get('transform_elapsed_s',progress.get('transform_elapsed_s'))
        row=dict(case=record['case'],arm=record['arm'],status=analysis['status'],transform_wall_s=analysis['transform_wall_s'],
            timing=timing,guidance_wall_s=guidance.get('guidance_wall_s',0),discovery_wall_s=guidance.get('discovery_wall_s',0),
            elapsed_timing_record_s=elapsed,unassigned_recorded_elapsed_s=elapsed-sum(timing.values())-guidance.get('guidance_wall_s',0),
            unassigned_caution='Not a persist timer; includes all uninstrumented work and incomplete active work on timeout',
            metrics={k:analysis['positive_funnel'].get(k,0)for k in ('searched_roots','actual_queries','requested_queries','solver_process_wall_s')},
            guidance_work={k:guidance.get(k,0)for k in ('refinement_searches','discovery_executed_roots',
                'discovery_skipped_unchanged_projection_roots','independently_replayed_models','free_only_search_rounds')})
        if record['arm']=='predecessor_free':
            row['saved_record_overhead']=account(case,analysis,plan['chunk_roots'],reader)
        rows.append(row)
    result=dict(status='COMPLETE_METADATA_ONLY',cases=rows,source_files=reader.bound,bytes_read=reader.bytes,
        accounting_wall_s=time.monotonic()-reader.start,no_solver_calls=True,no_runtime_replay=True,no_performance_code_edit=True,
        interpretation='Call/byte counts derived from saved ordered records and frozen control flow; no elapsed cost attributed to persist without a new approved instrumented experiment')
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
