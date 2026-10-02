#!/usr/bin/env python3
"""Execute one explicitly approved frozen paired pilot; never auto-rerun/expand."""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import time

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def write(path,value):
    path=Path(path);tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');tmp.replace(path)
def require(c,m):
    if not c:raise ValueError(m)
def candidate_id(c):return c['root'],tuple(c['recipe']),c['out']
def serialized(ids):return [[root,list(recipe),out] for root,recipe,out in sorted(ids)]
def proc_info(pid):
    try:
        root=Path('/proc')/str(pid);stat=(root/'stat').read_text().rsplit(')',1)[1].split()
        rss=next((int(line.split()[1]) for line in (root/'status').read_text().splitlines() if line.startswith('VmRSS:')),0)
        cmd=(root/'cmdline').read_bytes().split(b'\0')
        return dict(pid=pid,start=stat[19],pgid=int(stat[2]),rss_kib=rss,cmd=[x.decode(errors='replace') for x in cmd if x])
    except (FileNotFoundError,ProcessLookupError,PermissionError):return None

def descendants(pid):
    found={};todo=[pid]
    while todo:
        current=todo.pop()
        if current in found:continue
        info=proc_info(current)
        if info is None:continue
        found[current]=info
        try:
            for task in (Path('/proc')/str(current)/'task').iterdir():
                try:todo.extend(int(x) for x in (task/'children').read_text().split())
                except (FileNotFoundError,ProcessLookupError,PermissionError):pass
        except (FileNotFoundError,ProcessLookupError,PermissionError):pass
    return found

def stop_owned(process,owned):
    owned.update(descendants(process.pid))
    groups={}
    for pid,old in owned.items():
        now=proc_info(pid)
        if now and now['start']==old['start'] and now['pgid']==old['pgid'] and now['pgid'] in owned:
            groups[now['pgid']]=owned[now['pgid']]['start']
    for sig in (signal.SIGTERM,signal.SIGKILL):
        for pid,old in reversed(list(owned.items())):
            now=proc_info(pid)
            if now and now['start']==old['start']:
                try:os.kill(pid,sig)
                except ProcessLookupError:pass
        for group,leader_start in groups.items():
            if group==os.getpgrp():continue
            leader=proc_info(group)
            if leader is not None and leader['start']!=leader_start:continue
            # A terminated group leader does not remove surviving descendants.
            # A reused leader PID with a new start token is never signalled.
            try:os.killpg(group,sig)
            except ProcessLookupError:pass
        if sig==signal.SIGTERM:time.sleep(0.2)
    if process.poll() is None:process.kill()
    try:process.wait(timeout=5)
    except subprocess.TimeoutExpired:raise RuntimeError('owned controller process did not stop')

def execute(command,log_path,watchdog_seconds,worker_job=None):
    """Outer watchdog is infrastructure-only, never a transform-budget substitute."""
    start=time.monotonic();owned={};peak_all=peak_transform=0;samples=0;timeout=False
    with Path(log_path).open('w') as stream:
        process=subprocess.Popen(command,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
        owned.update(descendants(process.pid))
        try:
            while process.poll() is None:
                tree=descendants(process.pid);owned.update(tree);samples+=1
                peak_all=max(peak_all,sum(x['rss_kib'] for x in tree.values()))
                if worker_job:
                    for pid,info in tree.items():
                        cmd=info['cmd']
                        if '--worker-job' in cmd:
                            index=cmd.index('--worker-job')
                            if index+1<len(cmd) and cmd[index+1]==worker_job:
                                peak_transform=max(peak_transform,sum(x['rss_kib'] for x in descendants(pid).values()))
                if time.monotonic()-start>watchdog_seconds:
                    timeout=True;stop_owned(process,owned);break
                time.sleep(0.1)
        except BaseException:
            stop_owned(process,owned);raise
    return dict(command=command,exit_code=process.returncode,status='INFRASTRUCTURE_TIMEOUT' if timeout else 'EXIT',
                wall_s=time.monotonic()-start,log_sha256=sha(log_path),samples=samples,
                sampled_all_process_tree_peak_rss_kib=peak_all,sampled_transform_tree_peak_rss_kib=peak_transform or None,
                memory_note='100ms sampled RSS sum; shared pages double counted and short-lived peaks may be missed')

def collect_case(run,case):
    source=Path(run)/Path(case).stem;result=read(source/'result.json');candidates={};saved={}
    terminal=result.get('transform') or {};progress=result.get('last_completed_chunk') or {}
    guidance=terminal.get('image_guidance') or progress.get('image_guidance') or {}
    funnel=terminal.get('metrics') or progress.get('metrics') or {}
    admitted_chunks=max((read(source/'checkpoints'/n['directory']/'checkpoint.json')['progress'].get('proof_completed_chunks',0)
        for n in result['driver']['observed_checkpoints']),default=0)
    for path in sorted((source/'chunks').glob('chunk_*/candidates.json')):
        for c in read(path):
            identity=candidate_id(c);require(identity not in saved,'attempted candidate identity was retried');saved[identity]=c
            if result['status']=='COMPLETE' or int(path.parent.name[6:])<admitted_chunks:candidates[identity]=c
    roots=[json.loads(line) for line in (source/'root_search.jsonl').read_text().splitlines()] if (source/'root_search.jsonl').exists() else []
    selected=[]
    if result.get('selected_checkpoint'):selected=read(Path(result['selected_checkpoint']['directory'])/'selection.json')['selected']
    ids=set(candidates);qualified={i for i,c in candidates.items() if c.get('qualified_offline_opportunity')}
    appended={i for i,c in candidates.items() if c.get('free_witness',{}).get('lane',-1)>=256 and 'free_domain' in c}
    return dict(status=result['status'],search_complete=result.get('search_complete',False),
        root_pools={r['root']:[r['pool'],r['pool_info']] for r in roots},candidate_ids=serialized(ids),qualified_ids=serialized(qualified),
        all_complete_saved_candidate_ids=serialized(set(saved)),admitted_proof_chunk_prefix=admitted_chunks,
        candidate_count_scope='all COMPLETE-run proofs, otherwise only proof prefix covered by an on-time admitted checkpoint',
        selected_ids=serialized({candidate_id(c) for c in selected}),appended_witness_ids=serialized(appended),
        appended_witness_qualified_ids=serialized(appended&qualified),
        free_manifest_files=[dict(file=str(p.relative_to(source)),sha256=sha(p),free_version=read(p)['free_version'],
            free_domain_sha256=read(p)['free_domain_sha256'],added_worlds=len(read(p)['records'])) for p in sorted((source/'free_domains').glob('*.json'))],
        transform_wall_s=result['driver']['transform_process_wall_s'],transform_hard_cap_s=result['driver']['hard_transform_budget_s'],
        positive_funnel=funnel,guidance=guidance,
        guidance_evidence_source='transform' if terminal.get('image_guidance') else 'last_completed_chunk' if progress.get('image_guidance') else 'UNAVAILABLE',
        funnel_evidence_source='transform' if terminal.get('metrics') else 'last_completed_chunk' if progress.get('metrics') else 'UNAVAILABLE',
        original_result_sha256=sha(source/'result.json'),result=result)

def analyze(root,plan,ledger):
    by_key={(r['case'],r['arm']):r for r in ledger};rows=[]
    for case in plan['cases']:
        name=case['file'];pair={};failed=[]
        for arm in ('baseline','predecessor_free'):
            record=by_key.get((name,arm));pair[arm]=record
            if (not record or record.get('status')!='VALIDATED' or 'analysis' not in record or not record.get('global_result') or
                type(record['global_result'].get('global_hash_corrected_conditional_build_marginal')) is not int):failed.append(arm)
        row=dict(case=name,loaded_and=case['loaded_AND'],missing_or_failed_arms=failed)
        if not failed:
            base,free=[pair[a]['analysis'] for a in ('baseline','predecessor_free')]
            common=set(base['root_pools'])&set(free['root_pools'])
            require(all(base['root_pools'][r]==free['root_pools'][r] for r in common),'common root pools changed between arms')
            initial_hashes=[a['guidance'].get('pool_signature_sha256') for a in (base,free)]
            if all(initial_hashes):require(initial_hashes[0]==initial_hashes[1],'initial construction signatures differ')
            initial_identity='PASS' if all(initial_hashes) else 'UNAVAILABLE_BEFORE_GUIDANCE_REPORT'
            make=lambda rows:{(r,tuple(recipe),out) for r,recipe,out in rows}
            row.update(common_completed_roots=len(common),common_root_pool_identity='PASS' if common else 'NO_COMMON_ROOT_LOGS',initial_pool_signature_identity=initial_identity,
                new_retained_ids=serialized(make(free['candidate_ids'])-make(base['candidate_ids'])),
                new_qualified_ids=serialized(make(free['qualified_ids'])-make(base['qualified_ids'])),
                new_selected_ids=serialized(make(free['selected_ids'])-make(base['selected_ids'])),
                source_status={a:pair[a]['analysis']['status'] for a in pair},
                genuine_build_and={a:pair[a]['global_result']['global_hash_corrected_conditional_build_marginal'] for a in pair})
            values=row['genuine_build_and'];require(all(type(v)is int for v in values.values()),'unvalidated attribution')
            row['paired_and_difference']=values['predecessor_free']-values['baseline']
        rows.append(row)
    valid=[r for r in rows if not r['missing_or_failed_arms']]
    summary=dict(status='COMPLETE' if len(valid)==6 else 'INCOMPLETE_PAIRED_COVERAGE',cases=rows,valid_pairs=len(valid),
        fixed_cases=6,paired_and_difference=sum(r['paired_and_difference'] for r in valid) if valid else None,
        valid_pair_equal_case_percentage_point_difference=sum(100*r['paired_and_difference']/r['loaded_and'] for r in valid)/len(valid) if valid else None,
        native_novelty='NOT_CHECKED',no_automatic_full55=True,
        interpretation='Paired whole-original/selected-root-bounded-Direct-corrected genuine Build marginals; new IDs alone are not area gains. Missing arms are not zeros.')
    write(root/'summary.json',summary)

def run(plan_path,approved,expected_plan_sha256=None):
    require(approved,'Explicit GO required; supply --execute-approved-plan only after approval')
    require(type(expected_plan_sha256)is str and len(expected_plan_sha256)==64,'approved plan SHA256 is required')
    require(sha(plan_path)==expected_plan_sha256,'approved plan changed')
    root=Path(plan_path).resolve().parent;plan=read(plan_path)
    require(plan['status']=='PREPARED_NOT_EXECUTED' and plan['approval_required'] and plan['workers']==1 and not plan['inline_cone_check'],'wrong frozen protocol')
    require(not (root/'execution.json').exists(),'this frozen pilot was already started; no automatic retry')
    require(sha(plan['python'])==plan['python_sha256'],'Python executable changed')
    require(shutil.disk_usage(root).free>=6*1024**3,'pilot requires at least6GiB free workspace disk')
    for name,h in plan['source_freeze_sha256'].items():require(sha(root/name)==h,'prepared source/input/tool changed: '+name)
    write(root/'execution.json',dict(status='RUNNING',plan_sha256=sha(plan_path),started_unix=time.time(),explicit_go_gate=True))
    (root/'logs').mkdir();ledger=[]
    for ordinal,job in enumerate(plan['ordered_jobs']):
        record=dict(case=job['case'],arm=job['arm'],order=ordinal)
        run_dir=Path(job['directory']);stem=Path(job['case']).stem
        try:
            require(shutil.disk_usage(root).free>=1024**3,'less than1GiB free disk; preserve evidence and skip this fixed job')
            record['driver']=execute(job['command'],root/'logs'/f'{ordinal:02d}-transform.log',420,job['worker_job'])
            require(record['driver']['exit_code']==0,'case driver failed')
            require(read(run_dir/'source_integrity.json')['status']=='PASS','case source integrity failed')
            analysis=collect_case(run_dir,job['case']);record['analysis']=analysis
            require(analysis['status'] in ('COMPLETE','BUDGET_EXHAUSTED') and analysis['result'].get('product'),'no validated incumbent')
            product=analysis['result']['product'];require(product['baseline_dsec']['status']==product['independent_dsec']['status']=='PASS','baseline/product DSEC failed')
            record['baseline_product_dsec_wall_s']=sum(product[k]['wall_s'] for k in ('baseline_dsec','independent_dsec'))
            attribution=root/'audits'/stem/job['arm']/'direct';global_out=attribution.parent/'global';attribution.parent.mkdir(parents=True)
            command=[plan['python'],'-B',str(root/'source/image_cegar_diagnostic/audit_online_products.py'),'--run',str(run_dir),
                '--out',str(attribution),'--solver',str(root/'tools/solver'),'--abc',str(root/'tools/abc'),'--proof-seconds','120','--dsec-seconds','120']
            record['direct_audit_driver']=execute(command,root/'logs'/f'{ordinal:02d}-direct.log',900)
            require(record['direct_audit_driver']['exit_code']==0,'Direct audit failed')
            command=[plan['python'],'-B',str(root/'source/image_cegar_diagnostic/audit_global_alias_products.py'),'--attribution',str(attribution),
                '--out',str(global_out),'--abc',str(root/'tools/abc'),'--dsec-seconds','120']
            record['global_audit_driver']=execute(command,root/'logs'/f'{ordinal:02d}-global.log',900)
            require(record['global_audit_driver']['exit_code']==0,'whole-original audit failed')
            record['direct_result']=read(attribution/stem/'result.json');record['global_result']=read(global_out/stem/'result.json')
            require(record['global_result']['status']=='GLOBAL_STRUCTURAL_ALIAS_ACCOUNTING_COMPLETE','global attribution incomplete')
            require(type(record['global_result'].get('global_hash_corrected_conditional_build_marginal')) is int,
                    'global audit has no validated numeric marginal; preserve raw DSEC failure/UNKNOWN as missing')
            record['status']='VALIDATED'
        except Exception as error:
            record['status']='FAILED';record['error']=repr(error)
        ledger.append(record);write(root/'ledger.json',ledger)
        print(json.dumps(dict(case=job['case'],arm=job['arm'],status=record['status'],error=record.get('error'))),flush=True)
    for name,h in plan['source_freeze_sha256'].items():require(sha(root/name)==h,'prepared source/input/tool changed during run')
    analyze(root,plan,ledger)
    write(root/'execution.json',dict(status='FINISHED',finished_unix=time.time(),plan_sha256=sha(plan_path),
        jobs=len(ledger),validated=sum(r['status']=='VALIDATED' for r in ledger),original_protocol_unchanged=True))

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--plan',type=Path,required=True)
    ap.add_argument('--expected-plan-sha256',required=True)
    ap.add_argument('--execute-approved-plan',action='store_true');args=ap.parse_args();run(args.plan,args.execute_approved_plan,args.expected_plan_sha256)
