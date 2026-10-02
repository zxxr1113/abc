#!/usr/bin/env python3
"""Explicitly approved fresh audit-only repair of immutable paired transforms."""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import time

def read(path):return json.loads(Path(path).read_text())
def sha(path):
    digest=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):digest.update(chunk)
    return digest.hexdigest()
def require(condition,message):
    if not condition:raise ValueError(message)
def write(path,value):
    path=Path(path);tmp=path.with_suffix(path.suffix+'.tmp')
    tmp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');tmp.replace(path)
def check(plan):
    for name,digest in plan['bound_files'].items():require(sha(name)==digest,'bound file changed: '+name)

def run(path,expected,approved):
    require(approved,'explicit audit-only GO required')
    require(sha(path)==expected,'approved audit plan changed')
    root=path.resolve().parent;plan=read(path)
    require(plan['status']=='PREPARED_AUDIT_ONLY' and plan['workers']==1 and plan['transform_reruns']==0,'wrong scope')
    require(not (root/'execution.json').exists(),'audit repair already started; no automatic retry')
    require(shutil.disk_usage(root).free>=2*1024**3,'audit repair requires2GiB free')
    check(plan)
    original=Path(plan['original_root']);original_plan=read(original/'plan.json');old=read(original/'ledger.json')
    require(read(original/'execution.json')['status']=='FINISHED' and len(old)==12,'original run not terminal')
    spec=importlib.util.spec_from_file_location('frozen_pilot_controller',original/'run_prepared_pilot.py')
    controller=importlib.util.module_from_spec(spec);spec.loader.exec_module(controller)
    started=time.time();write(root/'execution.json',dict(status='RUNNING',started_unix=started,plan_sha256=expected,audit_only=True))
    (root/'logs').mkdir();ledger=[]
    jobs={(j['case'],j['arm']):j for j in plan['jobs']}
    require(len(jobs)==6 and all(arm=='predecessor_free'for _,arm in jobs),'only six treatment audits authorized')
    for prior in old:
        if prior['arm']=='baseline':
            require(prior['status']=='VALIDATED','original baseline audit is not validated')
            retained=copy.deepcopy(prior)
            retained.update(exact_baseline_audit_retained_from_v3=True,new_audit_cost_s=0)
            ledger.append(retained);write(root/'ledger.json',ledger)
            continue
        job=jobs[(prior['case'],prior['arm'])]
        record={key:copy.deepcopy(prior[key]) for key in ('case','arm','order','driver','analysis')}
        record.update(original_frozen_status=prior['status'],original_frozen_error=prior.get('error'),audit_only_repair=True)
        try:
            require(shutil.disk_usage(root).free>=1024**3,'less than1GiB free; preserve missingness')
            stem=Path(job['case']).stem;ordinal=record['order']
            Path(job['direct_out']).parent.mkdir(parents=True,exist_ok=True)
            record['direct_audit_driver']=controller.execute(job['direct_command'],root/'logs'/f'{ordinal:02d}-direct.log',900)
            require(record['direct_audit_driver']['exit_code']==0,'repaired Direct audit failed')
            record['global_audit_driver']=controller.execute(job['global_command'],root/'logs'/f'{ordinal:02d}-global.log',900)
            require(record['global_audit_driver']['exit_code']==0,'repaired whole-original audit failed')
            record['direct_result']=read(Path(job['direct_out'])/stem/'result.json')
            record['global_result']=read(Path(job['global_out'])/stem/'result.json')
            require(record['global_result']['status']=='GLOBAL_STRUCTURAL_ALIAS_ACCOUNTING_COMPLETE','incomplete global audit')
            require(type(record['global_result'].get('global_hash_corrected_conditional_build_marginal'))is int,
                    'unvalidated marginal remains missing')
            record['status']='VALIDATED'
        except Exception as error:
            record.update(status='FAILED',error=repr(error))
        ledger.append(record);write(root/'ledger.json',ledger)
        print(json.dumps({key:record.get(key)for key in ('case','arm','status','error')}),flush=True)
    check(plan)
    controller.analyze(root,original_plan,ledger)
    summary=read(root/'summary.json')
    summary.update(audit_only_repair=True,original_frozen_summary=str(original/'summary.json'),
        original_frozen_valid_pairs=read(original/'summary.json')['valid_pairs'],
        transform_outputs_unchanged=True,transform_reruns=0,
        exact_baseline_audits_retained_from_v3=True,
        added_audit_wall_s=sum(r.get(k,{}).get('wall_s',0)for r in ledger if r.get('audit_only_repair')
                              for k in ('direct_audit_driver','global_audit_driver')))
    write(root/'summary.json',summary)
    write(root/'execution.json',dict(status='FINISHED',started_unix=started,finished_unix=time.time(),
        plan_sha256=expected,audit_only=True,jobs=len(ledger),validated=sum(r['status']=='VALIDATED'for r in ledger),
        every_original_frozen_file_unchanged=True,transform_reruns=0))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan',type=Path,required=True);parser.add_argument('--expected-plan-sha256',required=True)
    parser.add_argument('--execute-approved-plan',action='store_true');args=parser.parse_args()
    run(args.plan,args.expected_plan_sha256,args.execute_approved_plan)
