#!/usr/bin/env python3
"""Freeze the agreed six-case paired pilot. This command never executes it."""
import argparse
import ast
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
CASES=['005_b03.aig','044_i2c.aig','041_des_area.aig','034_b20_opt.aig','045_mem_ctrl.aig','060_wb_dma.aig']
CONFIG=dict(pool_cap=24,reservoir_cap=128,tfi_depth=6,peer_hops=1,alias_cap=8,max_gates=2,
            candidates_per_root=8,lanes=256,seed=2026100201,wall_seconds=120.0)
AUDITORS=['image_cegar_diagnostic/audit_products.py','image_cegar_diagnostic/audit_online_products.py',
          'image_cegar_diagnostic/audit_global_alias_products.py','image_cegar_diagnostic/compare_attribution.py',
          'nonlinear_divisors/hash_direct_audit.py']
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write(path,obj):Path(path).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def runtime_list(name):
    tree=ast.parse((PACKAGE/name).read_text())
    return next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and
                any(isinstance(t,ast.Name) and t.id=='RUNTIME' for t in n.targets))
def orders():
    return [(name,['baseline','predecessor_free'] if i%2==0 else ['predecessor_free','baseline']) for i,name in enumerate(CASES)]
def prepare(out,solver,abc):
    start=time.monotonic();out=out.resolve();assert not out.exists(),'new prepared directory required';out.mkdir(parents=True)
    manifest_hash=sha(PACKAGE/'cases.json');manifest=json.loads((PACKAGE/'cases.json').read_text())
    assert sha(PACKAGE/'cases.json')==manifest_hash,'case manifest changed during read'
    all_cases={c['file']:c for c in manifest['cases']};cases=[all_cases[name] for name in CASES]
    runtime=[]
    controls=['nonlinear_divisors/anytime.py','nonlinear_divisors/image_guided.py','nonlinear_divisors/inline_models.py','nonlinear_divisors/free_guided.py']
    source_identity={name:sha(PACKAGE/name) for name in controls};source_identity['cases.json']=manifest_hash
    for name in controls:
        runtime.extend(runtime_list(name));assert sha(PACKAGE/name)==source_identity[name],'runtime source changed during parse'
    sources=sorted(set(runtime+AUDITORS+['cases.json']))
    for case in cases:sources.extend([case['first_seq_path'],case['loaded_path']])
    source=out/'source';bindings={}
    for name in sources:
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        destination=source/name;destination.parent.mkdir(parents=True,exist_ok=True);before=sha(PACKAGE/name)
        assert name not in source_identity or before==source_identity[name],'source changed before freeze'
        shutil.copy2(PACKAGE/name,destination)
        assert sha(destination)==before==sha(PACKAGE/name),'source changed during copy'
        bindings[str(destination.relative_to(out))]=before
    for case in cases:
        assert sha(source/case['first_seq_path'])==case['first_seq_sha256']
        assert sha(source/case['loaded_path'])==case['loaded_sha256']
    (out/'tools').mkdir()
    for name,path in [('solver',solver),('abc',abc)]:
        destination=out/'tools'/name;before=sha(path);shutil.copy2(path,destination)
        assert sha(destination)==before==sha(path),'tool changed during copy';bindings[str(destination.relative_to(out))]=before
    controller=out/'run_prepared_pilot.py';shutil.copy2(HERE/'run_prepared_pilot.py',controller);bindings[controller.name]=sha(controller)
    jobs=[]
    for case,arm_order in orders():
        for arm in arm_order:
            directory=out/'runs'/Path(case).stem/arm
            command=[sys.executable,'-B',str(source/'nonlinear_divisors/anytime.py'),'--case',case,
                '--inline-image-models','--solver',str(out/'tools/solver'),'--abc',str(out/'tools/abc'),
                '--workers','1','--chunk-roots','32','--dsec-seconds','120','--out',str(directory)]
            for key,value in CONFIG.items():command.extend(['--'+key.replace('_','-'),str(value)])
            if arm=='predecessor_free':command.append('--predecessor-free')
            jobs.append(dict(case=case,arm=arm,directory=str(directory),command=command,
                worker_job=str(directory/Path(case).stem/'job.json')))
    plan=dict(schema=1,prepared_at_utc=datetime.now(timezone.utc).isoformat(),status='PREPARED_NOT_EXECUTED',
        approval_required=True,source_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=PACKAGE,text=True).strip(),
        source_freeze_sha256=bindings,python=sys.executable,python_sha256=sha(sys.executable),cases=cases,ordered_jobs=jobs,
        config=CONFIG,workers=1,chunk_roots=32,conflicts_per_query=1000,global_added_free_cap=256,
        free_only_revisit_cap_per_chunk=1,predecessor_pi_field='previous_inputs',inline_cone_check=False,
        validator='existing full original graph validation, default; cone optimization not enabled',
        proof_class='free SAT plus reset0 UNSAT plus unrestricted one-step-image UNSAT, independent previous/current PI',
        witness_policy='absolute append-only lanes; full saved PI/RO, free hash/version/manifest and authenticated inline origin',
        candidate_policy='same initial pools/ranking/aliases/seed/normalization/cost/top8, cumulative qualified union, attempted/UNKNOWN unchanged',
        timing=dict(transform_seconds_per_case_arm=120,maximum_transform_budget_seconds=1440,
                    transform_boundary='existing anytime outer process-group supervisor plus cooperative inner deadline',
                    dsec_seconds_each=120,direct_proof_seconds=120,audits='extra cost, separately timed and reported',
                    no_concurrent_jobs=True),
        order_policy='fixed case order and alternating baseline/feature order by case; no repeats/tuning/replacement',
        capture=['raw failures and coverage','exact input/loaded/tool/source hashes','initial pool/signature identity',
                 'free versions/hash/world origins','positive discovery funnel','retained/proved/selected new IDs',
                 'sampled transform process-tree peak RSS','Direct/global/individual DSEC wall costs',
                 'same-selected-set genuine Build marginal and paired difference'],
        memory_policy='100ms sampled RSS sum of --worker-job process and descendants; shared pages double counted, short-lived peaks may be missed',
        analysis_boundary='new-ID counts alone are not area gain; genuine Build marginal is whole-original alias corrected with bounded selected-root Direct audit',
        disk_policy=dict(minimum_start_free_gib=6,minimum_each_job_free_gib=1,no_cleanup_or_retry=True),
        fresh_audit_policy='both arms invoke this newly frozen auditor without --reuse-audit; new Direct queries and whole-original classification; only same-run exact-bound DSEC reuse',
        no_automatic_full55=True,prepare_wall_s=time.monotonic()-start)
    write(out/'plan.json',plan);write(out/'approval_gate.json',dict(status='AWAITING_EXPLICIT_PARENT_GO',pilot_executed=False,
        plan_sha256=sha(out/'plan.json'),
        command=[sys.executable,'-B',str(controller),'--plan',str(out/'plan.json'),'--expected-plan-sha256',sha(out/'plan.json'),'--execute-approved-plan']))
    print(json.dumps(dict(status=plan['status'],plan=str(out/'plan.json'),jobs=len(jobs),execute_requires_explicit_GO=True)))
    return plan
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--solver',type=Path,required=True);ap.add_argument('--abc',type=Path,required=True)
    args=ap.parse_args();prepare(args.out,args.solver,args.abc)
