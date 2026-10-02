#!/usr/bin/env python3
"""Explicit-GO-only, single-worker timing of fixed saved semantic worklists.

Fresh processes give cold logical caches. Filesystem cache coldness is not
claimed. This never invokes a search, solver, DSEC, or optimizer transform.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

def check_deadline(deadline):
    if deadline is not None and time.monotonic()>=deadline:raise TimeoutError('case work budget exhausted')
def sha(path,deadline=None):
    check_deadline(deadline)
    h=hashlib.sha256()
    with Path(path).open('rb')as stream:
        while True:
            check_deadline(deadline);b=stream.read(1024*1024);check_deadline(deadline)
            if not b:break
            h.update(b)
    return h.hexdigest()
def read(path):return json.loads(Path(path).read_text())
def write(path,value):
    path=Path(path);tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');tmp.replace(path)
def require(value,message):
    if not value:raise ValueError(message)
def verify(bound,deadline=None):
    check_deadline(deadline)
    for path,h in bound.items():require(sha(path,deadline)==h,'frozen file changed: '+path)

def run(path,expected,approved):
    require(approved,'explicit parent GO required; preparation does not authorize timing')
    require(sha(path)==expected,'approved timing plan changed')
    root=path.resolve().parent;plan=read(path)
    require(plan['status']=='PREPARED_NOT_EXECUTED' and plan['workers']==1 and plan['jobs_per_case']==4 and
            plan['case_total_cap_s']==120 and len(plan['jobs'])==12,'wrong frozen timing scope')
    require(not (root/'execution.json').exists(),'already started; no automatic retry')
    require(shutil.disk_usage(root).free>=2*1024**3,'requires2GiB free; no automatic cleanup')
    preflight=time.monotonic();verify(plan['bound_files']);verify(plan['original_evidence_bound_files'])
    preflight_wall=time.monotonic()-preflight
    start=time.time();charged={case:0.0 for case in plan['cases']};ledger=[]
    write(root/'execution.json',dict(status='RUNNING',started_unix=start,plan_sha256=expected))
    (root/'logs').mkdir()
    for number,job in enumerate(plan['jobs']):
        record={k:job[k]for k in ('case','mode','round')};available=plan['case_total_cap_s']-charged[job['case']]
        if available<=0:
            record.update(status='SKIPPED_CASE_CAP',source_verification_run=False,charged_case_wall_s=0,
                          cleanup_wall_s=0,cumulative_case_wall_s=charged[job['case']])
            ledger.append(record);write(root/'ledger.json',ledger);print(json.dumps(record),flush=True);continue
        began=time.monotonic();deadline=began+available;process=None;stopped=None;cleanup=0.0
        try:
            record['source_verification_run']=True;verify(plan['bound_files'],deadline);check_deadline(deadline)
            require(shutil.disk_usage(root).free>=1024**3,'less than1GiB free')
            with (root/'logs'/f'{number:02d}.log').open('w')as log:
                check_deadline(deadline)
                launched=time.monotonic();process=subprocess.Popen(job['command'],stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
                try:process.wait(timeout=max(0.001,deadline-time.monotonic()))
                except subprocess.TimeoutExpired:
                    stopped=time.monotonic();cleanup_start=time.monotonic()
                    os.killpg(process.pid,signal.SIGKILL);process.wait();cleanup+=time.monotonic()-cleanup_start
                    raise TimeoutError('case cumulative hard cap reached')
                record['process_wall_s']=time.monotonic()-launched
                require(process.returncode==0,'worklist process failed; first output preserved')
            check_deadline(deadline)
            result=read(Path(job['out'])/'result.json')
            require(result['status']=='PASS_ORDERED_SAVED_SEMANTICS' and
                    result['events_sha256']==plan['expected_events_sha256'][job['case']],'semantic result changed')
            require(result['original_proof_source_hashes']==plan['original_proof_source_hashes'][job['case']],
                    'original proof identity was rewritten')
            record.update(status='PASS',result_sha256=sha(Path(job['out'])/'result.json'),
                          cache_report=result['cache_report'],events_sha256=result['events_sha256'])
            check_deadline(deadline)
        except Exception as error:record.update(status='MISSING_OR_FAILED',error=repr(error))
        finally:
            if stopped is None:stopped=time.monotonic()
            if process is not None and process.poll()is None:
                cleanup_start=time.monotonic();os.killpg(process.pid,signal.SIGKILL);process.wait();cleanup+=time.monotonic()-cleanup_start
        record['charged_case_wall_s']=stopped-began;record['cleanup_wall_s']=cleanup
        record['work_budget_overrun_s']=max(0,record['charged_case_wall_s']-available)
        charged[job['case']]+=record['charged_case_wall_s']
        record['cumulative_case_wall_s']=charged[job['case']];ledger.append(record);write(root/'ledger.json',ledger)
        print(json.dumps(record),flush=True)
    final_guard=time.monotonic();verify(plan['bound_files']);verify(plan['original_evidence_bound_files'])
    final_guard_wall=time.monotonic()-final_guard;cases=[]
    for case in plan['cases']:
        rows=[r for r in ledger if r['case']==case];complete=len(rows)==4 and all(r['status']=='PASS'for r in rows)
        row=dict(case=case,complete=complete,charged_case_wall_s=charged[case])
        if complete:
            values={mode:[r['process_wall_s']for r in rows if r['mode']==mode]for mode in ('default_old','optin_cache')}
            means={mode:sum(v)/len(v)for mode,v in values.items()}
            row.update(process_wall_s=values,mean_process_wall_s=means,
                       cache_minus_default_mean_s=means['optin_cache']-means['default_old'],
                       ratio_of_means=means['optin_cache']/means['default_old'])
        cases.append(row)
    write(root/'summary.json',dict(status='COMPLETE'if all(r['complete']for r in cases)else'INCOMPLETE',cases=cases,
        boundary=plan['timing_boundary'],logical_cache='COLD_FRESH_PROCESS_EVERY_JOB',filesystem_cold='NOT_CLAIMED',
        separate_controller_preflight_hash_s=preflight_wall,separate_controller_final_hash_s=final_guard_wall,
        separate_process_cleanup_s=sum(r.get('cleanup_wall_s',0)for r in ledger),
        cap_note='Per-case work stops at cumulative120s; deadline checks bracket1MiB hash reads. Scheduling/read overrun and process cleanup are explicit, never silently called work inside the cap.',
        solver_calls=0,DSEC_calls=0,search_runs=0,optimizer_transform_runs=0,no_area_gain_claim=True,
        repetitions='two prespecified opposite-order pairs per case; no statistical generalization'))
    write(root/'execution.json',dict(status='FINISHED',started_unix=start,finished_unix=time.time(),plan_sha256=expected,
        passed=sum(r['status']=='PASS'for r in ledger),jobs=len(ledger),frozen_bindings_unchanged=True,
        original_evidence_unchanged=True))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--plan',type=Path,required=True)
    parser.add_argument('--expected-plan-sha256',required=True);parser.add_argument('--execute-approved-plan',action='store_true')
    args=parser.parse_args();run(args.plan,args.expected_plan_sha256,args.execute_approved_plan)
