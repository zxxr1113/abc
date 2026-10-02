#!/usr/bin/env python3
"""Hard-supervised fixed-four-case diagnostic. Preparation does not execute it."""
from __future__ import annotations
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import traceback
sys.dont_write_bytecode = True
from common import *
from independent_aig import Aig, recipe as independent_recipe, witness as independent_witness
from search import search_unsampled
from proof import prove, revalidate_receipts

def verify_domains(p, a, ia, frozen, deadline):
    graph, base, step, reset = p.compile_graph(a)
    cfg = p.Config(**frozen['config'])
    (free, image, initial), mask = p.signatures(graph, [base, step, reset], cfg)
    require(free == frozen['initial_free_signatures'] and mask == frozen['initial_free_mask'],
            'initial free signatures do not reconstruct')
    seq = [x | (y << 256) for x, y in zip(image, initial)]
    offset = 512
    for lane, world in enumerate(frozen['initial_worlds']):
        deadline.remaining()
        vals = ia.values(world['inputs'], world['state'])
        require(vals == [(v >> lane) & 1 for v in free] == a.step(world['inputs'], world['state'])[2],
                'initial full-world independent replay differs')
    sources = [Path(k) for k in frozen['source_hashes'] if k.endswith('/models/replayed_models.json')]
    require(len(sources) == 1, 'ambiguous saved image model source')
    models = read(sources[0])
    require(digest(models) == frozen['source_model_order_sha256'] and len(models) == frozen['source_model_count'],
            'saved image model order changed')
    seen = {}
    for row in models:
        deadline.remaining()
        require(row['domain'] == 'unrestricted_one_step_image' and row['reachable_teacher'] is False,
                'image source domain changed')
        pred = ia.values(row['previous_inputs'], row['previous_state'])
        state = ia.successor(pred)
        require(state == row['successor_state'], 'saved image transition replay differs')
        vals = ia.values(row['current_inputs'], state)
        root, recipe, out = row['candidate_id']
        require(vals == a.step(row['current_inputs'], state)[2], 'independent image all-node replay differs')
        require(vals[root] == row['root_value'] and independent_recipe(recipe, out, vals) == row['recipe_value']
                and row['root_value'] != row['recipe_value'], 'saved image root relation replay differs')
        key = tuple(row['current_inputs'] + state)
        if key not in seen:
            seen[key] = len(seen)
            for i, value in enumerate(vals):
                seq[i] |= value << offset
            offset += 1
        require(row['sample_index'] == seen[key], 'saved successor deduplication order differs')
    seq_mask = (1 << offset)-1
    require(seq == frozen['sequence_signatures'] and seq_mask == frozen['sequence_mask'],
            'post-first-refinement sequence snapshot does not reconstruct')
    return free, mask, seq, seq_mask, cfg

def baseline_qualified(frozen, baseline):
    oldpaths = [Path(k) for k in frozen['source_hashes'] if k.endswith('/chunks/chunk_00000/candidates.json')]
    newpaths = [Path(k) for k in frozen['source_hashes'] if k.endswith('/new_proofs/candidates.json')]
    require(len(oldpaths) == len(newpaths) == 1, 'ambiguous baseline proof sources')
    evidence = {}
    for path in oldpaths+newpaths:
        for c in read(path):
            if c.get('qualified_offline_opportunity'):
                proof = c.get('diagnostic_proof', c.get('proof'))
                require(proof['free'] == 'SAT' and proof['reset'] == 'UNSAT' and
                        proof.get('image', proof.get('step')) == 'UNSAT', 'saved qualified proof inconsistent')
                evidence[cid(c)] = dict(candidate_id=[c['root'], c['recipe'], c['out']],
                                        historical_certificate_file=str(path),
                                        historical_certificate_sha256=frozen['source_hashes'][str(path)],
                                        proof_reused=True, fresh_proof=False)
    return [evidence[cid(c)] for c in baseline if cid(c) in evidence]

def worker(case, solver, out, end, expected_manifest):
    out = Path(out)
    out.mkdir()  # Never overwrite even a failed attempt.
    deadline, started = Deadline(end), time.monotonic()
    timing = {}
    try:
        manifest = read(expected_manifest)
        launch_plan = read(Path(expected_manifest).parent/'plan.json')
        require(sha(solver) == launch_plan['solver_sha256'] and
                sha(str(solver)+'.build.json') == launch_plan['solver_build_sha256'], 'reviewed solver/build changed before worker')
        require(source_manifest() == manifest, 'diagnostic implementation drift')
        frozen, expected, snapshot, bindings = authenticate(case, deadline)
        for name, expected_hash in manifest.items():
            bindings.add(HERE/name, expected_hash)
        bindings.add(expected_manifest)
        build_path = Path(str(solver)+'.build.json')
        build = read(build_path)
        require(build['schema'] == 2 and build['conflicts_per_query'] == 1000 and build['projection_phase'] == 'free', 'wrong solver protocol')
        require(build['source_sha256'] == sha(HERE/'free_model_solver.c'), 'solver built from different source')
        prebuild_path = Path(str(solver)+'.prebuild.json')
        require(sha(prebuild_path) == build['prebuild_sha256'] and
                str(prebuild_path.resolve()) in build['files'], 'missing or changed prebuild binding')
        prebuild = read(prebuild_path)
        require(prebuild['commands'] == build['commands'] and prebuild['compiler_versions'] == build['compiler_versions'] and
                all(build['files'].get(k) == v for k, v in prebuild['files'].items()), 'pre/post build binding differs')
        for path, expected_hash in build['files'].items():
            bindings.add(path, expected_hash)
        bindings.add(build_path)
        bindings.add(solver, build['solver_sha256'])
        p = load_runtime(frozen)
        a, ia = p.Aiger(frozen['input']), Aig(frozen['input'])
        free, mask, seq, seq_mask, cfg = verify_domains(p, a, ia, frozen, deadline)
        timing['preparation_wall_s'] = time.monotonic()-started
        baseline, root_rows, totals = [], [], Counter()
        s = p.Structure(a)
        search_start = time.monotonic()
        for row in frozen['roots']:
            deadline.remaining()
            info = {int(k): v for k, v in row['pool_info'].items()}
            found, stats = p.search_root(s, row['root'], row['pool'], info, seq, seq_mask, free, mask, cfg, deadline)
            for c in found:
                c['free_witness'] = p.witness(a, c, free)
                independent_witness(ia, c, c['free_witness'], free)
            baseline.extend(found)
            root_rows.append(dict(root=row['root'], search=dict(stats), candidates=len(found)))
            totals.update(stats)
        timing['baseline_search_and_witness_wall_s'] = time.monotonic()-search_start
        require(baseline == expected, 'unchanged baseline identity/cost/witness reproduction failed')
        expected_rows = [json.loads(line) for line in (snapshot/'A_roots.jsonl').read_text().splitlines()]
        require(root_rows == expected_rows, 'unchanged baseline per-root counters differ')
        require(dict(totals) == read(snapshot/'result.json')['arms']['A']['stats'], 'baseline aggregate counters differ')
        write_new(out/'baseline_candidates.json', baseline)
        write_new(out/'baseline_roots.json', root_rows)
        qold = baseline_qualified(frozen, baseline)
        require(len(qold) == read(snapshot/'result.json')['arms']['A']['known_qualified'], 'baseline qualified set differs')
        write_new(out/'baseline_qualified_references.json', qold)
        unsampled, unsampled_rows, ranks = [], [], []
        search_start = time.monotonic()
        s = p.Structure(a)
        for row in frozen['roots']:
            deadline.remaining()
            found, stats, observed = search_unsampled(p, s, row, seq, seq_mask, free, mask, cfg,
                                                     deadline, SENTINELS if case == '045_mem_ctrl' else ())
            unsampled.extend(found)
            unsampled_rows.append(dict(root=row['root'], search=stats, candidates=len(found)))
            ranks.extend(observed)
        timing['unsampled_search_wall_s'] = time.monotonic()-search_start
        require(len(unsampled) <= 256 and len({cid(c) for c in unsampled}) == len(unsampled), 'candidate cap/identity violated')
        require(not ({cid(c) for c in baseline} & {cid(c) for c in unsampled}), 'frontiers overlap')
        require(all(p.recipe_eval(c['recipe'], c['out'], free, mask) == free[c['root']] for c in unsampled),
                'witnessed candidate entered unsampled lane')
        require(digest(dict(seq=seq, mask=seq_mask)) == frozen['sequence_sha256'] and
                digest(dict(free=free, mask=mask)) == frozen['arms']['A']['free_domain_sha256'], 'search changed a domain')
        write_new(out/'unsampled_candidates.json', unsampled)
        write_new(out/'unsampled_roots.json', unsampled_rows)
        write_new(out/'sentinel_ranks.json', ranks)
        proof_start = time.monotonic()
        proved, report = prove(p, a, ia, unsampled, solver, out/'proof', deadline, bindings.files)
        timing['proof_and_binding_wall_s'] = time.monotonic()-proof_start
        receipt_audit = revalidate_receipts(p, a, ia, proved, out/'proof', deadline)
        write_new(out/'receipt_audit.json', receipt_audit)
        qnew = [c for c in proved if c['qualified_offline_opportunity']]
        write_new(out/'cumulative_qualified_union.json', dict(baseline=qold, additional=qnew,
            baseline_retained=len(qold), additional_retained=len(qnew), baseline_reproved=False,
            retired_qualified=0, interpretation='Cumulative identity union; no selection or measured area'))
        bindings.check(deadline)
        deadline.remaining()
        result = dict(schema=1, case=case, status='COMPLETE', timing=timing,
            baseline_reproduction='PASS', initial256_unchanged=True, sequence_unchanged=True,
            baseline_candidates=len(baseline), baseline_qualified=len(qold),
            additional_candidates=len(unsampled), additional_qualified=len(qnew),
            free_queries=report['free_queries'], proof_queries=report['total_queries'],
            sentinel_ranks=ranks, source_integrity='PASS', source_bindings=bindings.files,
            exact_area=None, product_generated=False, dsec_run=False, native_novelty='NOT_CHECKED',
            worker_elapsed_s=time.monotonic()-started,
            output_artifacts={str(f.relative_to(out)): sha(f) for f in sorted(out.rglob('*')) if f.is_file()})
        write_new(out/'result.json', result)
        deadline.remaining()
        print(json.dumps(dict(status='COMPLETE', case=case, result_sha256=sha(out/'result.json'))), flush=True)
        return 0
    except BaseException as e:
        failure = dict(case=case, status='TIMEOUT' if isinstance(e, (TimeoutError, subprocess.TimeoutExpired)) else 'ERROR',
                       error=repr(e), traceback=traceback.format_exc(), elapsed_s=time.monotonic()-started)
        write_new(out/'failure.json', failure)
        print(json.dumps(dict(status=failure['status'], failure_sha256=sha(out/'failure.json'))), flush=True)
        return 2

def supervise(command, out, seconds):
    """Owned process group, hard deadline, no accepted post-deadline result."""
    started = time.monotonic()
    with (Path(out)/'worker.log').open('x') as log:
        proc = subprocess.Popen(command(started+seconds), stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        timed_out = False
        try:
            proc.wait(timeout=max(0.001, started+seconds-time.monotonic()))
        except subprocess.TimeoutExpired:
            timed_out = True
        finally:
            # Kill all members, including a solver or escaped-wait worker child.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()
        elapsed = time.monotonic()-started
    return dict(returncode=proc.returncode, timed_out=timed_out or elapsed > seconds,
                launch_through_exit_wall_s=elapsed, seconds=seconds)

def accept_completed(case, workdir, logdir, manifest):
    """Use the externally captured completion digest, then its complete artifact tree."""
    lines=(Path(logdir)/'worker.log').read_text().splitlines()
    notices=[]
    for line in lines:
        try:
            value=json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value,dict) and value.get('status')=='COMPLETE':
            notices.append(value)
    require(len(notices)==1 and notices[0].get('case')==case, 'missing/duplicate/wrong worker completion notice')
    workdir=Path(workdir)
    require(sha(workdir/'result.json')==notices[0]['result_sha256'], 'completed result changed after captured notice')
    result=read(workdir/'result.json')
    require(result['status']=='COMPLETE' and result['case']==case, 'bad worker completion')
    require(source_manifest()==manifest, 'implementation changed after worker')
    expected=result['output_artifacts']
    actual={str(f.relative_to(workdir)):sha(f) for f in sorted(workdir.rglob('*'))
            if f.is_file() and str(f.relative_to(workdir))!='result.json'}
    require(expected==actual, 'completed output artifact tree changed')
    Bindings(result['source_bindings']).check()
    report=read(workdir/'proof/report.json')
    Bindings(report['bindings']).check()
    audit=read(workdir/'receipt_audit.json')
    candidates=read(workdir/'proof/candidates.json')
    union=read(workdir/'cumulative_qualified_union.json')
    require(audit['status']=='PASS' and audit['candidates']==len(candidates)==report['candidate_count'] and
            result['additional_candidates']==len(candidates)==report['free_queries']==result['free_queries'],
            'completed candidate/audit count mismatch')
    require(result['proof_queries']==report['total_queries']==audit['queries'] and
            result['free_queries']<=256 and result['proof_queries']<=768, 'completed query count/cap mismatch')
    require(result['additional_qualified']==report['qualified']==len(union['additional'])==
            sum(c['qualified_offline_opportunity'] for c in candidates), 'completed qualification count mismatch')
    require(union['baseline']==read(workdir/'baseline_qualified_references.json') and
            union['baseline_retained']==result['baseline_qualified']==len(union['baseline']), 'baseline union changed')
    return result

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--solver', type=Path, required=True)
    ap.add_argument('--review', type=Path)
    ap.add_argument('--parent-go', choices=['RUN_FIXED_FIRST32'])
    ap.add_argument('--worker-case', choices=CASES)
    ap.add_argument('--deadline', type=float)
    ap.add_argument('--manifest', type=Path)
    args = ap.parse_args()
    if args.worker_case:
        require(args.deadline is not None and args.manifest is not None, 'worker requires supervisor bindings')
        return worker(args.worker_case, args.solver.resolve(), args.out, args.deadline, args.manifest)
    require(args.review is not None and args.parent_go == 'RUN_FIXED_FIRST32', 'separate source review and explicit parent GO required')
    manifest = source_manifest()
    review = read(args.review)
    require(review['status'] == 'PASS' and review['source_manifest_sha256'] == digest(manifest) and
            review['protocol_sha256'] == sha(HERE/'protocol.json') and
            review['solver_sha256'] == sha(args.solver) and
            review['solver_build_sha256'] == sha(str(args.solver)+'.build.json'),
            'review not bound to current implementation/protocol/solver/build')
    require(not args.out.exists(), 'new experiment directory required')
    args.out.mkdir(parents=True)
    write_new(args.out/'source_manifest.json', manifest)
    write_new(args.out/'plan.json', dict(protocol=read(HERE/'protocol.json'), source_manifest=manifest,
        review=str(args.review.resolve()), review_sha256=sha(args.review), solver=str(args.solver.resolve()),
        solver_sha256=sha(args.solver), solver_build_sha256=sha(str(args.solver)+'.build.json'), parent_go=args.parent_go, original_evidence_modified=False))
    rows = []
    for case in CASES:
        # One log directory and one separate worker result directory per attempt.
        logdir = args.out/case
        logdir.mkdir()
        workdir = logdir/'work'
        record = supervise(lambda end: [sys.executable, '-B', str(HERE/'run.py'),
            '--worker-case', case, '--deadline', str(end), '--manifest', str(args.out/'source_manifest.json'),
            '--solver', str(args.solver.resolve()), '--out', str(workdir)], logdir, 120)
        post_start = time.monotonic()
        if record['timed_out']:
            status = 'TIMEOUT'
        elif record['returncode'] != 0:
            status = 'ERROR'
        else:
            try:
                accept_completed(case, workdir, logdir, manifest)
                status = 'COMPLETE'
            except BaseException as e:
                status = 'ERROR'
                write_new(logdir/'acceptance_failure.json', dict(error=repr(e), traceback=traceback.format_exc()))
        row = dict(case=case, status=status, supervisor=record, post_case_validation_wall_s=time.monotonic()-post_start)
        rows.append(row)
        write_new(logdir/'supervisor.json', row)
        print(json.dumps(row), flush=True)
        if status == 'ERROR':
            break  # Integrity/provenance failures halt the protocol, with untouched first failure.
    write_new(args.out/'summary.json', dict(cases=rows, full_protocol_complete=len(rows) == 4,
        area_measured=False, no_online_or_full55_expansion=True))
    return 0 if len(rows) == 4 and all(r['status'] == 'COMPLETE' for r in rows) else 2
if __name__ == '__main__':
    raise SystemExit(main())
