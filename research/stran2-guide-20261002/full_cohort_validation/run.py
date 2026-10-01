#!/usr/bin/env python3
"""Prepare a fixed all55 protocol; execute only after explicit post-v3 approval.

Uses existing anytime/auditor CLIs unchanged. Each matched two-case block has
one arm wave at a time. No outcome-dependent selection or completion reordering.
"""
from __future__ import annotations
import argparse
import ast
from collections import Counter
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import socket
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
CONFIG = dict(pool_cap=24, reservoir_cap=128, tfi_depth=6, peer_hops=1,
              alias_cap=8, max_gates=2, candidates_per_root=8, lanes=256,
              seed=2026100201, wall_seconds=120.0)
ARMS = ('ordinary', 'imageguided')
EXTRA = ['nonlinear_divisors/hash_direct_audit.py',
         'image_cegar_diagnostic/audit_online_products.py',
         'image_cegar_diagnostic/audit_global_alias_products.py',
         'image_cegar_diagnostic/audit_products.py',
         'seq_care_cut2/query_solver.c', 'build_query_solver.sh']
ENV = dict(PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0', OMP_NUM_THREADS='1',
           OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1', LC_ALL='C')
GIB = 1024 ** 3
CAPACITY = HERE / 'capacity_basis.json'


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, data):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    tmp.replace(path)


def assignment(path, name):
    for node in ast.parse(Path(path).read_text()).body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in node.targets):
            return ast.literal_eval(node.value)
    raise ValueError('missing literal ' + name)


def waves(cases):
    result = []
    for block, i in enumerate(range(0, len(cases), 2)):
        names = [r['file'] for r in cases[i:i + 2]]
        for arm in ARMS if block % 2 == 0 else ARMS[::-1]:
            result.append(dict(wave=len(result), block=block, arm=arm, cases=names,
                               relative_run=f'runs/block_{block:03d}/{arm}'))
    return result


def header_and(path):
    with Path(path).open('rb') as f:
        fields = f.readline().split()
    require(fields[0] in (b'aig', b'aag') and len(fields) == 6, 'ordinary AIGER required: ' + str(path))
    return int(fields[5])


def freeze(args):
    manifest = PACKAGE / 'cases.json'
    cases = read(manifest)['cases']
    require(len(cases) == 55 and len({r['file'] for r in cases}) == 55, 'exactly 55 unique cases required')
    for r in cases:
        for kind in ('first_seq', 'loaded'):
            path = PACKAGE / r[kind + '_path']
            require(sha(path) == r[kind + '_sha256'], 'input SHA mismatch: ' + str(path))
            require(header_and(path) == r[kind + '_AND'], 'input AND mismatch: ' + str(path))
    runtime = assignment(PACKAGE / 'nonlinear_divisors/anytime.py', 'RUNTIME')
    image_runtime = assignment(PACKAGE / 'nonlinear_divisors/image_guided.py', 'RUNTIME')
    sources = sorted(set(runtime + image_runtime + EXTRA))
    config_ast = ast.parse((PACKAGE / 'nonlinear_divisors/prototype.py').read_text())
    actual = next({n.target.id: ast.literal_eval(n.value) for n in cls.body if isinstance(n, ast.AnnAssign)}
                  for cls in config_ast.body if isinstance(cls, ast.ClassDef) and cls.name == 'Config')
    require(actual == CONFIG, 'Config defaults changed; review protocol, do not silently retune')
    for file in ('seq_care_cut2/query_solver.c', 'image_cegar_diagnostic/model_solver.c'):
        require('sat_solver_solve(s,lits,lits+n,1000,0,0,0)' in (PACKAGE / file).read_text(), 'solver conflict source changed')
    tools = {name: dict(path=str(path.resolve()), sha256=sha(path), bytes=path.stat().st_size)
             for name, path in [('solver', args.solver), ('image_model_solver', args.image_model_solver), ('abc', args.abc)]}
    protocol = dict(schema=1, readiness='PREPARED_ONLY_REQUIRES_EXPLICIT_GO_AFTER_V3_REVIEW',
        package=str(PACKAGE), manifest_sha256=sha(manifest), cases=cases, waves=waves(cases),
        source_hashes={name: sha(PACKAGE / name) for name in sources}, tools=tools,
        runner_sha256=sha(__file__), config=CONFIG, workers=2, chunk_roots=32,
        dsec_seconds=120.0, direct_proof_seconds=120.0, conflicts_per_query=1000,
        environment_overrides=ENV, scheduling='manifest-order two-case blocks; serial matched arm waves; alternate first arm',
        scope='55 frozen first_seq graphs only; ordinary anytime vs opt-in imageguided; no native-baseline or raw typed HWMCC claim',
        metric='paired global_hash_corrected_conditional_build_marginal / original loaded_AND; bounded Direct audit plus whole-original structural alias demotion',
        attribution_cost='separate from transform; audit every planned case, preserve errors and missingness',
        resource_policy=capacity_policy(tools), capacity_basis_sha256=sha(CAPACITY),
        observation=dict(host=socket.gethostname(), python=sys.version, platform=platform.platform()))
    require(not args.protocol.exists(), 'new protocol path required')
    write(args.protocol, protocol)
    print(json.dumps(dict(protocol=str(args.protocol), sha256=sha(args.protocol), cases=55, transforms=110, executed=False)))


def capacity_policy(tools):
    basis = read(CAPACITY)
    evidence_per_case = sum(basis['largest_case_bytes'].values())
    tool_bytes = sum(row['bytes'] for row in tools.values())
    # All 110 case-arms at the largest observed evidence size, plus 25% growth.
    estimate = int(110 * evidence_per_case * 1.25) + tool_bytes + 4 * GIB
    return dict(worst_observed_scenario_bytes=estimate,
                initial_free_disk_bytes=4 * GIB + int(4 * evidence_per_case * 1.25) + tool_bytes + 16 * 1024 ** 2,
                block_free_disk_bytes=4 * GIB + int(4 * evidence_per_case * 1.25),
                wave_free_disk_bytes=4 * GIB + int(2 * evidence_per_case * 1.25),
                per_case_pending_audit_bytes=int(sum(basis['largest_case_bytes'][k] for k in ('direct_audit', 'global_audit')) * 1.25),
                min_mem_available_bytes=4 * GIB, output_tmpfs_allowed=False,
                capacity_basis=basis, growth_factor=1.25,
                estimate_is_hard_upper_bound=False, admission='one full paired block plus all deferred audit reserves',
                checks='paired-block boundary, and emergency wave floor; not a hard allocation cap')


def filesystem_type(path):
    path = Path(path).resolve()
    matches = []
    for line in Path('/proc/mounts').read_text().splitlines():
        parts = line.split()
        mount = Path(parts[1].replace('\\040', ' '))
        if path == mount or mount in path.parents:
            matches.append((len(mount.parts), parts[2]))
    return max(matches)[1] if matches else 'unknown'


def resources(path, policy, initial=False, required_bytes=None):
    memory = {line.split(':')[0]: int(line.split()[1]) * 1024
              for line in Path('/proc/meminfo').read_text().splitlines() if ':' in line}
    data = dict(free_disk_bytes=shutil.disk_usage(path).free,
                mem_available_bytes=memory['MemAvailable'], filesystem=filesystem_type(path))
    require(data['filesystem'] != 'tmpfs', 'output on tmpfs is prohibited')
    data['required_free_disk_bytes'] = required_bytes if required_bytes is not None else policy['initial_free_disk_bytes' if initial else 'wave_free_disk_bytes']
    require(data['free_disk_bytes'] >= data['required_free_disk_bytes'],
            'insufficient free disk for conservative frozen-cohort retention policy')
    require(data['mem_available_bytes'] >= policy['min_mem_available_bytes'],
            'less than 4 GiB available memory; wait for other work')
    return data


def verify(protocol, package, tools):
    require(sha(package / 'cases.json') == protocol['manifest_sha256'], 'manifest drift')
    for name, digest in protocol['source_hashes'].items():
        require(sha(package / name) == digest, 'source drift: ' + name)
    for r in protocol['cases']:
        for kind in ('first_seq', 'loaded'):
            require(sha(package / r[kind + '_path']) == r[kind + '_sha256'], 'input drift: ' + r['file'])
    for name, path in tools.items():
        require(sha(path) == protocol['tools'][name]['sha256'], 'tool drift: ' + name)


def copy_frozen(protocol, out):
    package = Path(protocol['package'])
    original_tools = {name: Path(row['path']) for name, row in protocol['tools'].items()}
    verify(protocol, package, original_tools)
    files = set(protocol['source_hashes']) | {'cases.json'}
    files |= {r[k + '_path'] for r in protocol['cases'] for k in ('first_seq', 'loaded')}
    frozen = out / 'frozen_package'
    for name in sorted(files):
        dest = frozen / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(package / name, dest)
        dest.chmod(0o444)
    tools = {}
    (out / 'tools').mkdir()
    for name, path in original_tools.items():
        tools[name] = out / 'tools' / name
        shutil.copyfile(path, tools[name])
        tools[name].chmod(0o555)
    verify(protocol, frozen, tools)
    return frozen, tools


def transform_command(protocol, frozen, tools, wave, out):
    command = [sys.executable, '-B', str(frozen / 'nonlinear_divisors/anytime.py'),
               '--cases', *wave['cases'], '--solver', str(tools['solver']), '--abc', str(tools['abc']),
               '--out', str(out / wave['relative_run']), '--workers', '2', '--chunk-roots', '32', '--dsec-seconds', '120']
    for key, value in protocol['config'].items():
        command.extend(['--' + key.replace('_', '-'), str(value)])
    if wave['arm'] == 'imageguided':
        command.extend(['--image-model-solver', str(tools['image_model_solver'])])
    return command


def execute(command, log):
    start = time.monotonic()
    with log.open('x') as stream:
        rc = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT,
                            env=dict(os.environ, **ENV), check=False).returncode
    return dict(command=command, exit_code=rc, outer_wall_s=time.monotonic() - start)


def ledger(protocol):
    return [dict(file=r['file'], loaded_and=r['loaded_AND'], arm=arm, status='NOT_STARTED',
                 search_complete=False, product=None) for r in protocol['cases'] for arm in ARMS]


def merge_wave(rows, wave, result_rows):
    received = {r['file']: r for r in result_rows}
    require(len(received) == len(result_rows) and set(received) <= set(wave['cases']), 'unexpected/duplicate result rows')
    for row in rows:
        if row['arm'] == wave['arm'] and row['file'] in wave['cases']:
            incoming = received.get(row['file'], dict(status='ERROR', search_complete=False, product=None,
                                                       error='wave exited without a result row'))
            row.update(incoming, wave=wave['wave'], relative_run=wave['relative_run'])


def pending_wave(rows, wave):
    matched = [r for r in rows if r['arm'] == wave['arm'] and r['file'] in wave['cases']]
    require(len(matched) == len(wave['cases']), 'missing wave ledger rows')
    unstarted = [r['status'] == 'NOT_STARTED' for r in matched]
    require(all(unstarted) or not any(unstarted), 'ambiguous partially started wave')
    require(not any(r['status'] == 'RUNNING' for r in matched), 'ambiguous RUNNING wave')
    return all(unstarted)


def validate_resume(protocol, out, rows, history, executions, frozen, tools):
    require(history and history[-1]['status'] == 'CAPACITY_STOP', 'resume requires recorded capacity stop')
    require(str(out) == history[0]['output_root'], 'original absolute output root required')
    require(sha(out / 'protocol.json') == history[0]['protocol_sha256'], 'resume protocol drift')
    require(sha(out / 'results.json') == history[-1]['ledger_sha256'], 'resume ledger drift')
    require((out / 'integrity.json').exists() and read(out / 'integrity.json')['status'] == 'PASS',
            'resume requires a completed immutable snapshot; initial pre-snapshot stop needs a fresh output')
    require(sha(out / 'executions.json') == history[-1]['executions_sha256'], 'resume execution journal drift')
    expected = {(r['file'], arm) for r in protocol['cases'] for arm in ARMS}
    require(len(rows) == len(expected) and {(r['file'], r['arm']) for r in rows} == expected, 'resume case ledger differs')
    by_wave = {e['wave']['wave']: e for e in executions}
    require(len(by_wave) == len(executions), 'duplicate execution journal entry')
    for wave in protocol['waves']:
        path = out / wave['relative_run']
        if pending_wave(rows, wave):
            require(not path.exists() and wave['wave'] not in by_wave, 'unstarted wave has ambiguous existing artifacts')
            require(not (out / 'logs' / f"wave_{wave['wave']:03d}.log").exists(), 'unstarted wave already has a driver log')
        else:
            require(wave['wave'] in by_wave and by_wave[wave['wave']]['wave'] == wave, 'completed wave missing exact journal')
            entry = by_wave[wave['wave']]
            for name, digest in entry['bound_run_files'].items():
                require(sha(path / name) == digest, 'completed wave metadata drift: ' + str(path / name))
    verify(protocol, frozen, tools)


def transform(args, resuming=False):
    protocol = read(args.protocol)
    require(sha(__file__) == protocol['runner_sha256'], 'runner changed since protocol freeze')
    if resuming:
        rows = read(args.out / 'results.json')
        history = read(args.out / 'attempt_history.json')
        executions = read(args.out / 'executions.json')
        frozen = args.out / 'frozen_package'
        tools = {name: args.out / 'tools' / name for name in protocol['tools']}
        validate_resume(protocol, args.out, rows, history, executions, frozen, tools)
    else:
        require(not args.out.exists(), 'new output directory required; use explicit resume only after a capacity stop')
        args.out.mkdir()
        shutil.copyfile(args.protocol, args.out / 'protocol.json')
        rows, history, executions = ledger(protocol), [], []
        write(args.out / 'results.json', rows)
        write(args.out / 'executions.json', executions)
    history.append(dict(invocation=len(history), mode='resume' if resuming else 'transform', status='RUNNING',
                        output_root=str(args.out), protocol_sha256=sha(args.out / 'protocol.json'),
                        started_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())))
    write(args.out / 'attempt_history.json', history)
    stopped = False

    def stop_for_capacity(error, wave, required):
        nonlocal stopped
        stopped = True
        stop = dict(status='CAPACITY_STOP', next_wave=wave['wave'], next_block=wave['block'],
                    reason=str(error), required_free_disk_bytes=required,
                    actual_free_disk_bytes=shutil.disk_usage(args.out).free,
                    remaining_not_started=sum(r['status'] == 'NOT_STARTED' for r in rows),
                    message='Capacity stop: remaining planned cases are NOT_STARTED, not failures or zero gain. Review storage before explicit resume.')
        directory = args.out / 'capacity_stops'
        directory.mkdir(exist_ok=True)
        write(directory / f"invocation_{len(history)-1:03d}.json", stop)
        write(args.out / 'capacity_stop.json', stop)
        history[-1].update(status='CAPACITY_STOP', capacity_stop=stop)
        print(json.dumps(stop), flush=True)

    try:
        if not resuming:
            try:
                resources(args.out, protocol['resource_policy'], initial=True)
            except ValueError as error:
                stop_for_capacity(error, protocol['waves'][0], protocol['resource_policy']['initial_free_disk_bytes'])
                return
            frozen, tools = copy_frozen(protocol, args.out)
            (args.out / 'logs').mkdir()
        for wave in protocol['waves']:
            if not pending_wave(rows, wave):
                continue
            policy = protocol['resource_policy']
            deferred = sum(r['status'] != 'NOT_STARTED' for r in rows) * policy['per_case_pending_audit_bytes']
            required = policy['block_free_disk_bytes'] + deferred if wave['wave'] % 2 == 0 else policy['wave_free_disk_bytes'] + deferred
            try:
                state = resources(args.out, policy, required_bytes=required)
            except ValueError as error:
                stop_for_capacity(error, wave, required)
                break
            verify(protocol, frozen, tools)
            command = transform_command(protocol, frozen, tools, wave, args.out)
            for row in rows:
                if row['arm'] == wave['arm'] and row['file'] in wave['cases']:
                    row.update(status='RUNNING', wave=wave['wave'], relative_run=wave['relative_run'])
            write(args.out / 'results.json', rows)
            attempt = execute(command, args.out / 'logs' / f"wave_{wave['wave']:03d}.log")
            run = args.out / wave['relative_run']
            result_path = run / 'results.json'
            merge_wave(rows, wave, read(result_path) if result_path.exists() else [])
            attempt.update(wave=wave, resource_before=state,
                           bound_run_files={name: sha(run / name) for name in ('plan.json', 'results.json', 'source_integrity.json')
                                            if (run / name).exists()})
            executions.append(attempt)
            write(args.out / 'executions.json', executions)
            write(args.out / 'results.json', rows)
            print(json.dumps(dict(wave=wave['wave'], arm=wave['arm'], exit_code=attempt['exit_code'])), flush=True)
        verify(protocol, frozen, tools)
        write(args.out / 'integrity.json', dict(status='PASS', all_waves_attempted=all(r['status'] != 'NOT_STARTED' for r in rows)))
        if not stopped:
            history[-1]['status'] = 'ALL_PLANNED_WAVES_ATTEMPTED'
    except BaseException as error:
        for row in rows:
            if row['status'] == 'RUNNING':
                row.update(status='ERROR', error='orchestration interrupted: ' + repr(error))
        write(args.out / 'results.json', rows)
        history[-1].update(status='ERROR', error=repr(error))
        write(args.out / 'interruption.json', dict(error=repr(error), unattempted=sum(r['status'] == 'NOT_STARTED' for r in rows)))
        raise
    finally:
        history[-1].update(ledger_sha256=sha(args.out / 'results.json'), executions_sha256=sha(args.out / 'executions.json'))
        write(args.out / 'attempt_history.json', history)
        write(args.out / 'run_state.json', dict(status=history[-1]['status'], invocation=len(history)-1))
        write(args.out / 'coverage.json', dict(planned=110, statuses=dict(Counter(r['status'] for r in rows)),
              missing_data_are_zero=False, corrected_metric_status='REQUIRES_SEPARATE_AUDITS'))


def resume(args):
    args.protocol = args.out / 'protocol.json'
    transform(args, resuming=True)


def audit(args):
    protocol = read(args.out / 'protocol.json')
    require(sha(__file__) == protocol['runner_sha256'], 'runner changed since protocol freeze')
    require(read(args.out / 'integrity.json')['status'] == 'PASS', 'complete transform integrity required before audit')
    frozen = args.out / 'frozen_package'
    tools = {name: args.out / 'tools' / name for name in protocol['tools']}
    verify(protocol, frozen, tools)
    audit_root = args.out / 'audits'
    audit_root.mkdir()
    summarize(args)
    for wave in protocol['waves']:
        try:
            resources(args.out, protocol['resource_policy'])
        except ValueError as error:
            stop = dict(status='CAPACITY_STOP', next_audit_wave=wave['wave'], reason=str(error))
            write(audit_root / 'capacity_stop.json', stop)
            print(json.dumps(stop), flush=True)
            break
        run = args.out / wave['relative_run']
        if not (run / 'plan.json').exists():
            write(audit_root / f"wave_{wave['wave']:03d}_not_started.json", dict(status='NOT_STARTED', wave=wave, reason='no transform run plan'))
            continue
        direct = audit_root / f"wave_{wave['wave']:03d}_direct"
        global_out = audit_root / f"wave_{wave['wave']:03d}_global"
        helper = frozen / 'image_cegar_diagnostic'
        commands = [
            [sys.executable, '-B', str(helper / 'audit_online_products.py'), '--run', str(run), '--out', str(direct),
             '--solver', str(tools['solver']), '--abc', str(tools['abc']), '--proof-seconds', '120', '--dsec-seconds', '120'],
            [sys.executable, '-B', str(helper / 'audit_global_alias_products.py'), '--attribution', str(direct),
             '--out', str(global_out), '--abc', str(tools['abc']), '--dsec-seconds', '120']]
        for label, command in zip(('direct', 'global'), commands):
            attempt = execute(command, audit_root / f"wave_{wave['wave']:03d}_{label}.log")
            write(audit_root / f"wave_{wave['wave']:03d}_{label}.attempt.json", attempt)
        summarize(args)
    verify(protocol, frozen, tools)
    write(audit_root / 'integrity.json', dict(status='PASS'))


def summarize(args):
    protocol = read(args.out / 'protocol.json')
    transform_rows = {(r['file'], r['arm']): r for r in read(args.out / 'results.json')}
    joined = {(r['file'], arm): dict(file=r['file'], loaded_and=r['loaded_AND'], arm=arm,
                                   transform_status=transform_rows[(r['file'], arm)]['status'],
                                   transform_search_complete=transform_rows[(r['file'], arm)].get('search_complete', False),
                                   transform_dsec={key: (transform_rows[(r['file'], arm)].get('product') or {}).get(key, {}).get('status', 'NOT_RUN')
                                                   for key in ('baseline_dsec', 'independent_dsec')},
                                   direct_audit_status='MISSING', direct_unknown_queries=None,
                                   audit_status='MISSING', corrected_gain=None)
              for r in protocol['cases'] for arm in ARMS}
    for wave in protocol['waves']:
        direct = args.out / 'audits' / f"wave_{wave['wave']:03d}_direct" / 'results.json'
        if direct.exists():
            for r in read(direct):
                target = joined[(r['case'] + '.aig', wave['arm'])]
                target.update(direct_audit_status=r['status'],
                              direct_unknown_queries=r.get('direct_proof', {}).get('unknown_not_cached', 0) if r['status'] == 'ATTRIBUTION_AUDIT_COMPLETE' else None,
                              direct_dsec={name: arm.get('dsec', {}).get('status', 'NOT_RUN') for name, arm in r.get('arms', {}).items()})
        path = args.out / 'audits' / f"wave_{wave['wave']:03d}_global" / 'results.json'
        if path.exists():
            for r in read(path):
                target = joined[(r['case'] + '.aig', wave['arm'])]
                integrity = path.parent / 'integrity.json'
                trusted = integrity.exists() and read(integrity)['status'] == 'PASS'
                target.update(audit_status=r['status'] if trusted else 'INCOMPLETE_INTEGRITY',
                              global_dsec={label: {name: product.get(name, {}).get('dsec', {}).get('status', 'NOT_RUN')
                                                  for name in ('full', 'without_genuinely_new_build')} for label, product in r.get('products', {}).items()},
                              corrected_gain=r.get('global_hash_corrected_conditional_build_marginal') if trusted else None)
    paired = []
    for r in protocol['cases']:
        pair = [joined[(r['file'], arm)] for arm in ARMS]
        if all(x['corrected_gain'] is not None and x['transform_status'] in ('COMPLETE', 'BUDGET_EXHAUSTED') for x in pair):
            paired.append(dict(file=r['file'], loaded_and=r['loaded_AND'], ordinary=pair[0]['corrected_gain'],
                               imageguided=pair[1]['corrected_gain'], delta=pair[1]['corrected_gain'] - pair[0]['corrected_gain'],
                               no_unknown_in_bounded_direct_audits=all(x['direct_unknown_queries'] == 0 for x in pair)))
    def stats(rs):
        return dict(cases=len(rs), ordinary_gain=sum(r['ordinary'] for r in rs), imageguided_gain=sum(r['imageguided'] for r in rs),
                    delta_and=sum(r['delta'] for r in rs),
                    ordinary_equal_case_percent=100 * sum(r['ordinary'] / r['loaded_and'] for r in rs) / len(rs) if rs else None,
                    imageguided_equal_case_percent=100 * sum(r['imageguided'] / r['loaded_and'] for r in rs) / len(rs) if rs else None,
                    weighted_delta_percent=100 * sum(r['delta'] for r in rs) / sum(r['loaded_and'] for r in rs) if rs else None,
                    equal_case_delta_pp=100 * sum(r['delta'] / r['loaded_and'] for r in rs) / len(rs) if rs else None)
    largest = max(paired, key=lambda r: r['delta'], default=None)
    write(args.out / 'corrected_rows.json', list(joined.values()))
    write(args.out / 'corrected_summary.json', dict(planned_cases=55, planned_transforms=110, paired=stats(paired), paired_rows=paired,
        excluded_cases=[r['file'] for r in protocol['cases'] if r['file'] not in {p['file'] for p in paired}],
        excluding_largest_positive_delta_case=stats([r for r in paired if r is not largest]) if largest and largest['delta'] > 0 else stats(paired),
        by_loaded_size={name: stats([r for r in paired if lo <= r['loaded_and'] < hi]) for name, lo, hi in
            [('lt1k', 0, 1000), ('1k_to_10k', 1000, 10000), ('10k_to_100k', 10000, 100000), ('ge100k', 100000, float('inf'))]},
        audit_statuses=dict(Counter(r['audit_status'] for r in joined.values())),
        direct_unknown_queries_by_arm={arm: sum(r['direct_unknown_queries'] or 0 for r in joined.values() if r['arm'] == arm) for arm in ARMS},
        paired_no_direct_unknown_sensitivity=stats([r for r in paired if r['no_unknown_in_bounded_direct_audits']]),
        missing_data_are_zero=False,
        scope=protocol['scope'], attribution_cost=protocol['attribution_cost'], native_recipe_novelty='NOT_CHECKED'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest='stage', required=True)
    p = subs.add_parser('freeze')
    p.add_argument('--protocol', type=Path, required=True)
    p.add_argument('--solver', type=Path, required=True)
    p.add_argument('--image-model-solver', type=Path, required=True)
    p.add_argument('--abc', type=Path, required=True)
    p = subs.add_parser('transform')
    p.add_argument('--protocol', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--approved-after-v3-review', action='store_true', required=True)
    p = subs.add_parser('resume')
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--approved-after-v3-review', action='store_true', required=True)
    p = subs.add_parser('audit')
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--approved-after-v3-review', action='store_true', required=True)
    p = subs.add_parser('summarize')
    p.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if hasattr(args, 'out'):
        args.out = args.out.resolve()
    # One transform/audit invocation at a time; coordinate unrelated work separately.
    with Path('/workspace/shared/stran2_full_cohort.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        globals()[args.stage](args)
    if args.stage in ('transform', 'resume') and read(args.out / 'run_state.json')['status'] == 'CAPACITY_STOP':
        return 2
    return 2 if args.stage == 'audit' and (args.out / 'audits/capacity_stop.json').exists() else 0


if __name__ == '__main__':
    raise SystemExit(main())
