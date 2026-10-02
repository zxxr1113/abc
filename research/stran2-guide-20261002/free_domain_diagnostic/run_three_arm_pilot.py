#!/usr/bin/env python3
"""Explicitly approved three-arm pilot; all formal audits are fresh same-run."""
import argparse
import json
from pathlib import Path
import shutil
import time

from run_prepared_pilot import read,write,sha,require,collect_case
from pilot_process import execute

ARMS=('inline_free_off','predecessor_cache_off','predecessor_cache_on')
CONTRASTS={
    'free_without_cache_minus_inline':('inline_free_off','predecessor_cache_off'),
    'cache_effect_minus_uncached_free':('predecessor_cache_off','predecessor_cache_on'),
    'cached_free_minus_inline':('inline_free_off','predecessor_cache_on')}

class DiskCapacityStop(RuntimeError):
    pass

class DiskGuard:
    """Capacity guard, not an estimate of this process's physical disk writes."""
    def __init__(self, root, policy, usage=None):
        self.root=root;self.policy=policy;self.usage=usage or shutil.disk_usage
        self.largest_job_consumption=0;self.job_start=None;self.observations=[]
    def free(self):return self.usage(self.root).free
    def start(self):
        free=self.free();required=self.policy['minimum_start_free_gib']*1024**3
        if free<required:raise DiskCapacityStop('insufficient start disk')
        return dict(free_bytes=free,required_bytes=required)
    def begin_job(self):self.job_start=self.free();self.observations=[]
    def check(self,stage):
        free=self.free();current=max(0,self.job_start-free)
        observed=max(self.largest_job_consumption,current)
        allowance=max(self.policy['minimum_job_growth_allowance_gib']*1024**3,
                      self.policy['observed_growth_multiplier']*observed)
        required=self.policy['reserve_gib']*1024**3+allowance
        row=dict(stage=stage,free_bytes=free,required_bytes=required,growth_allowance_bytes=allowance,
                 largest_observed_job_free_space_consumption_bytes=observed,passes=free>=required)
        self.observations.append(row)
        if not row['passes']:raise DiskCapacityStop('capacity reserve/growth check failed before '+stage)
    def finish_job(self):
        free=self.free();growth=max(0,self.job_start-free)
        self.largest_job_consumption=max(self.largest_job_consumption,growth)
        return dict(start_free_bytes=self.job_start,end_free_bytes=free,
                    observed_free_space_consumption_bytes=growth,checks=list(self.observations),
                    note='Filesystem free-space delta; not process-attributed writes or an output-size bound.')

def ids(rows):return {(root,tuple(recipe),out)for root,recipe,out in rows}
def serialized(values):return [[r,list(recipe),out]for r,recipe,out in sorted(values)]
def valid(record):
    return bool(record and record.get('status')=='VALIDATED' and type(record.get('global_result',{}).get(
        'global_hash_corrected_conditional_build_marginal'))is int)

def analyze(plan,ledger):
    indexed={(r['case'],r['arm']):r for r in ledger};cases=[]
    for case in plan['cases']:
        name=case['file'];records={arm:indexed.get((name,arm))for arm in ARMS};row=dict(case=name,loaded_and=case['loaded_AND'],arms={},contrasts={})
        for arm,record in records.items():
            row['arms'][arm]=dict(status=record.get('status')if record else'MISSING',
                genuine_build_and=record['global_result']['global_hash_corrected_conditional_build_marginal']if valid(record)else None)
        for label,(before,after)in CONTRASTS.items():
            a,b=records[before],records[after];missing=[arm for arm in (before,after)if not valid(records[arm])]
            comparison=dict(before=before,after=after,missing_or_failed_arms=missing)
            if not missing:
                x,y=a['analysis'],b['analysis'];common=set(x['root_pools'])&set(y['root_pools'])
                require(all(x['root_pools'][r]==y['root_pools'][r]for r in common),'common frozen pools differ')
                initial=[z['guidance'].get('pool_signature_sha256')for z in (x,y)]
                if all(initial):require(initial[0]==initial[1],'initial construction signatures differ')
                comparison.update(paired_and_difference=row['arms'][after]['genuine_build_and']-row['arms'][before]['genuine_build_and'],
                    common_completed_roots=len(common),common_pool_identity='PASS'if common else'NO_COMMON_ROOT_LOGS',
                    initial_signature_identity='PASS'if all(initial)else'UNAVAILABLE_BEFORE_GUIDANCE_REPORT',
                    new_retained_ids=serialized(ids(y['candidate_ids'])-ids(x['candidate_ids'])),
                    new_qualified_ids=serialized(ids(y['qualified_ids'])-ids(x['qualified_ids'])),
                    new_selected_ids=serialized(ids(y['selected_ids'])-ids(x['selected_ids'])),
                    transform_status={before:x['status'],after:y['status']})
            row['contrasts'][label]=comparison
        cases.append(row)
    aggregates={}
    for label in CONTRASTS:
        pairs=[r for r in cases if not r['contrasts'][label]['missing_or_failed_arms']]
        aggregates[label]=dict(valid_pairs=len(pairs),fixed_cases=6,
            paired_and_difference=sum(r['contrasts'][label]['paired_and_difference']for r in pairs)if pairs else None,
            valid_pair_equal_case_percentage_point_difference=(sum(100*r['contrasts'][label]['paired_and_difference']/r['loaded_and']for r in pairs)/len(pairs))if pairs else None)
    return dict(status='COMPLETE'if all(v['valid_pairs']==6 for v in aggregates.values())else'INCOMPLETE_PAIRED_COVERAGE',
        cases=cases,contrasts=aggregates,no_automatic_full55=True,native_novelty='NOT_CHECKED',
        interpretation='Same-current-runtime paired contrasts under the120s cap, including cost and coverage effects; fresh whole-original and selected-root-bounded-Direct corrected Build marginals. Missing arms are not zeros; new IDs alone are not area gains.')

def run(path,expected,approved):
    require(approved,'explicit parent GO required');require(sha(path)==expected,'approved plan changed')
    root=path.resolve().parent;plan=read(path)
    require(plan['status']=='PREPARED_NOT_EXECUTED'and plan['workers']==1 and not plan['inline_cone_check']and
            len(plan['ordered_jobs'])==18 and tuple(plan['arms'])==ARMS,'wrong frozen three-arm scope')
    require(not(root/'execution.json').exists(),'already started; no automatic retry')
    disk=DiskGuard(root,plan['disk_policy']);disk_start=disk.start()
    def verify():
        for name,h in plan['source_freeze_sha256'].items():require(sha(root/name)==h,'prepared source/input changed: '+name)
        for name,h in plan['external_bindings'].items():require(sha(name)==h,'bound tool/reference changed: '+name)
    verify();started=time.time();write(root/'execution.json',dict(status='RUNNING',started_unix=started,plan_sha256=expected,disk_start=disk_start))
    (root/'logs').mkdir();ledger=[];capacity_stop=None
    for ordinal,job in enumerate(plan['ordered_jobs']):
        record=dict(case=job['case'],arm=job['arm'],order=ordinal);run_dir=Path(job['directory']);stem=Path(job['case']).stem
        if capacity_stop is not None:
            record.update(status='SKIPPED_DISK_CAPACITY',error=capacity_stop)
            ledger.append(record);write(root/'ledger.json',ledger)
            print(json.dumps(record),flush=True);continue
        disk.begin_job()
        try:
            disk.check('transform')
            record['driver']=execute(job['command'],root/'logs'/f'{ordinal:02d}-transform.log',420,job['worker_job'])
            require(record['driver']['exit_code']==0,'case driver failed')
            require(read(run_dir/'source_integrity.json')['status']=='PASS','source integrity failed')
            record['analysis']=collect_case(run_dir,job['case']);result=record['analysis']['result']
            require(result['status']in('COMPLETE','BUDGET_EXHAUSTED')and result.get('product'),'no validated incumbent')
            product=result['product'];require(product['baseline_dsec']['status']==product['independent_dsec']['status']=='PASS','initial product DSEC failed')
            record['baseline_product_dsec_wall_s']=sum(product[k]['wall_s']for k in('baseline_dsec','independent_dsec'))
            direct=root/'audits'/stem/job['arm']/'direct';global_out=direct.parent/'global';direct.parent.mkdir(parents=True)
            command=[plan['python'],'-B',str(root/'source/image_cegar_diagnostic/audit_online_products.py'),'--run',str(run_dir),
                     '--out',str(direct),'--solver',plan['solver'],'--abc',plan['abc'],'--proof-seconds','120','--dsec-seconds','120']
            disk.check('Direct audit')
            record['direct_audit_driver']=execute(command,root/'logs'/f'{ordinal:02d}-direct.log',900)
            require(record['direct_audit_driver']['exit_code']==0,'fresh Direct audit failed')
            command=[plan['python'],'-B',str(root/'source/image_cegar_diagnostic/audit_global_alias_products.py'),'--attribution',str(direct),
                     '--out',str(global_out),'--abc',plan['abc'],'--dsec-seconds','120']
            disk.check('whole-original audit')
            record['global_audit_driver']=execute(command,root/'logs'/f'{ordinal:02d}-global.log',900)
            require(record['global_audit_driver']['exit_code']==0,'fresh whole-original audit failed')
            record['direct_result']=read(direct/stem/'result.json');record['global_result']=read(global_out/stem/'result.json')
            require(record['global_result']['status']=='GLOBAL_STRUCTURAL_ALIAS_ACCOUNTING_COMPLETE','incomplete attribution')
            require(type(record['global_result'].get('global_hash_corrected_conditional_build_marginal'))is int,
                    'DSEC UNKNOWN/failure leaves marginal missing')
            record['status']='VALIDATED'
        except DiskCapacityStop as error:
            capacity_stop=repr(error);record.update(status='DISK_CAPACITY_STOP',error=capacity_stop)
        except Exception as error:record.update(status='FAILED',error=repr(error))
        finally:record['disk']=disk.finish_job()
        ledger.append(record);write(root/'ledger.json',ledger)
        print(json.dumps({k:record.get(k)for k in('case','arm','status','error')}),flush=True)
    verify();write(root/'summary.json',analyze(plan,ledger))
    write(root/'execution.json',dict(status='FINISHED',started_unix=started,finished_unix=time.time(),jobs=len(ledger),
          validated=sum(r['status']=='VALIDATED'for r in ledger),plan_sha256=expected,source_and_tools_unchanged=True,
          disk_start=disk_start,capacity_stop=capacity_stop))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--plan',type=Path,required=True)
    parser.add_argument('--expected-plan-sha256',required=True);parser.add_argument('--execute-approved-plan',action='store_true')
    args=parser.parse_args();run(args.plan,args.expected_plan_sha256,args.execute_approved_plan)
