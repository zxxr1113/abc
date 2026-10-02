#!/usr/bin/env python3
"""Prepare the agreed18-job pilot; this script cannot execute it."""
import argparse
from datetime import datetime,timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys
from prepare_pilot import CASES,CONFIG,AUDITORS,runtime_list,sha,write,PACKAGE,HERE
from run_three_arm_pilot import ARMS

RUNTIME_COMMIT='b04f4ca3aab332939adccb84b51c3e5babccb76c'

def orders():
    first=[list(ARMS[i:]+ARMS[:i])for i in range(3)]
    return list(zip(CASES,first+[list(reversed(row))for row in first]))

def prepare(out,solver,abc,rss_manifest,recovery_manifest):
    out=out.resolve();assert out.is_relative_to(Path('/workspace/scratch/7e0c7273599c')),'scratch-only recovery output required'
    assert not out.exists();out.mkdir(parents=True)
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=PACKAGE,text=True).strip()
    manifest_hash=sha(PACKAGE/'cases.json');manifest=json.loads((PACKAGE/'cases.json').read_text())
    assert sha(PACKAGE/'cases.json')==manifest_hash
    cases=[next(row for row in manifest['cases']if row['file']==name)for name in CASES]
    controls=['nonlinear_divisors/'+name+'.py'for name in('anytime','image_guided','inline_models','free_guided','free_manifest_cache')]
    runtime=[]
    for name in controls:runtime.extend(runtime_list(name))
    sources=sorted(set(runtime+AUDITORS+['cases.json']))
    for case in cases:sources.extend([case['first_seq_path'],case['loaded_path']])
    frozen={};source=out/'source'
    for name in sources:
        assert not Path(name).is_absolute()and '..'not in Path(name).parts
        path=PACKAGE/name;h=sha(path)
        committed=subprocess.check_output(['git','show',RUNTIME_COMMIT+':research/stran2-guide-20261002/'+name],cwd=PACKAGE)
        import hashlib
        assert hashlib.sha256(committed).hexdigest()==h,'runtime/input differs from reviewed commit: '+name
        target=source/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(path,target)
        assert sha(path)==sha(target)==h;frozen[str(target.relative_to(out))]=h
    for case in cases:
        assert sha(source/case['first_seq_path'])==case['first_seq_sha256']
        assert sha(source/case['loaded_path'])==case['loaded_sha256']
    for name in ('run_three_arm_pilot.py','run_prepared_pilot.py','pilot_process.py','prepare_three_arm_pilot.py','prepare_pilot.py',
                 'test_pilot_process.py','test_three_arm_pilot.py'):
        path=HERE/name;h=sha(path);target=out/name;shutil.copy2(path,target)
        assert sha(path)==sha(target)==h;frozen[name]=h
    rss_manifest=rss_manifest.resolve();rss=json.loads(rss_manifest.read_text())
    assert rss['status']=='PASS'and rss['monitor_sha256']==frozen['pilot_process.py'],'RSS evidence source differs'
    external={str(solver.resolve()):sha(solver),str(abc.resolve()):sha(abc),sys.executable:sha(sys.executable),str(rss_manifest):sha(rss_manifest)}
    recovery_manifest=recovery_manifest.resolve();recovery=json.loads(recovery_manifest.read_text())
    assert recovery['status']=='RECOVERY_TESTS_PASS'
    assert recovery['solver']['path']==str(solver.resolve())and recovery['solver']['sha256']==sha(solver)
    assert recovery['abc']['path']==str(abc.resolve())and recovery['abc']['sha256']==sha(abc)
    for report in (rss,recovery):
        for path,h in report['bound_files'].items():
            assert sha(path)==h,'validation evidence changed: '+path
            external[path]=h
    external[str(recovery_manifest)]=sha(recovery_manifest)
    jobs=[]
    for name,arms in orders():
        for arm in arms:
            directory=out/'runs'/Path(name).stem/arm
            command=[sys.executable,'-B',str(source/'nonlinear_divisors/anytime.py'),'--case',name,'--inline-image-models',
                '--solver',str(solver.resolve()),'--abc',str(abc.resolve()),'--workers','1','--chunk-roots','32',
                '--dsec-seconds','120','--out',str(directory)]
            for key,value in CONFIG.items():command.extend(['--'+key.replace('_','-'),str(value)])
            if arm!='inline_free_off':command.append('--predecessor-free')
            if arm=='predecessor_cache_on':command.append('--free-manifest-cache')
            jobs.append(dict(case=name,arm=arm,directory=str(directory),command=command,worker_job=str(directory/Path(name).stem/'job.json')))
    plan=dict(schema=1,status='PREPARED_NOT_EXECUTED',approval_required=True,prepared_at_utc=datetime.now(timezone.utc).isoformat(),
        source_head=head,runtime_commit=RUNTIME_COMMIT,source_freeze_sha256=frozen,external_bindings=external,python=sys.executable,
        solver=str(solver.resolve()),abc=str(abc.resolve()),cases=cases,arms=list(ARMS),ordered_jobs=jobs,config=CONFIG,
        workers=1,chunk_roots=32,conflicts_per_query=1000,global_added_free_cap=256,free_only_revisit_cap_per_chunk=1,
        predecessor_pi_field='previous_inputs',inline_cone_check=False,validator='FULL compiled original-model validation in all arms',
        proof_class='free SAT; reset0 UNSAT; unrestricted one-step image UNSAT; previous/current PI independent',
        candidate_policy='identical frozen initial pools/seed/normalization/cost/top8; cumulative qualified union and attempted/UNKNOWN unchanged',
        order_policy='three cyclic arm orders, then their reversals; every arm occupies each position twice and each pair order is balanced',
        timing=dict(transform_seconds_per_case_arm=120,maximum_transform_budget_seconds=2160,independent_dsec_seconds_each=120,
                    direct_proof_seconds=120,audits='fresh extra cost after each arm, separately reported',
                    boundary='existing cooperative inner deadline plus hard outer process-group supervisor; no concurrent heavy jobs'),
        audit_policy='all18 arms freshly invoke repaired auditor without --reuse-audit and fresh whole-original alias classification; only exact same-run graph-bound DSEC reuse; no historical baseline',
        witness_policy='absolute append-only lanes; reconstruct complete saved domains and authenticate original model provenance; discovery/final domain hashes need not match',
        rss_validation=dict(file=str(rss_manifest),sha256=sha(rss_manifest)),
        tool_recovery_validation=dict(file=str(recovery_manifest),sha256=sha(recovery_manifest),
            same_binary_as_historical=True,historical_paths_not_rewritten=True),
        memory_policy='PPid/start-token owned process tree; exact expected --worker-job match;100ms requested sampling plus observer overhead; shared pages double counted, short-lived peaks missed, partial/ambiguous samples remain missing',
        sampling_cost='same collector in all arms; observer work stays inside wrapper wall/CPU contention and is never subtracted from120s worker deadlines',
        disk_policy=dict(minimum_start_free_gib=16,planning_allowance_gib=12,reserve_gib=4,
            minimum_job_growth_allowance_gib=2,observed_growth_multiplier=2,no_automatic_cleanup=True,
            observed_free_bytes_at_preparation=shutil.disk_usage(out).free,
            checks='before every transform and audit; fail closed and skip remaining jobs on capacity failure',
            growth_observation='before/after filesystem free-space delta, including current partial job consumption; not process-attributed writes',
            limitation='12GiB is a planning allowance, not a measured output bound. Historic exact per-arm sizes unavailable after shared storage loss. Pre-stage checks do not impose a within-process write quota.'),
        environment_recovery='Shared storage was lost; this is a fresh scratch-only plan with re-bound tools and surviving committed inputs. Historical raw outputs remain unavailable references. All18 arms run in this current environment; no cross-recovery historical timing contrast.',
        interpretation='Same-current-runtime paired contrasts: predecessor-free without cache versus inline includes cost and coverage under120s; cache-on versus cache-off; cached predecessor-free versus inline. Saved-worklist speedups do not establish area gains.',
        timing_caveat='sub-50ms small differences can be polling/scheduling resolution; report b03-type small changes as unresolved, not reliable slowdown',
        no_automatic_full55=True,no_retuning_or_retries=True,no_case_replacement=True)
    write(out/'plan.json',plan);fingerprint=sha(out/'plan.json')
    write(out/'approval_gate.json',dict(status='AWAITING_EXPLICIT_PARENT_GO',executed=False,plan_sha256=fingerprint,
        command=[sys.executable,'-B',str(out/'run_three_arm_pilot.py'),'--plan',str(out/'plan.json'),
                 '--expected-plan-sha256',fingerprint,'--execute-approved-plan']))
    return plan

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--solver',type=Path,required=True);parser.add_argument('--abc',type=Path,required=True)
    parser.add_argument('--rss-manifest',type=Path,required=True)
    parser.add_argument('--recovery-manifest',type=Path,required=True);args=parser.parse_args()
    result=prepare(args.out,args.solver,args.abc,args.rss_manifest,args.recovery_manifest)
    print(json.dumps(dict(status=result['status'],jobs=len(result['ordered_jobs']),plan=str(args.out/'plan.json'))))
