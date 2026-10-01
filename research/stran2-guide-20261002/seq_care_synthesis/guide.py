#!/usr/bin/env python3
"""Paired, independently audited Strict guide experiments on saved joint inputs.

No production source or historical product is modified. All attempts, including
timeouts and unknown proofs, stay in their own case directory. Instrumented
transform wall time is work accounting, not a production speed measurement.
"""
import argparse
import collections
import concurrent.futures
import csv
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OLD = Path('/mnt/home/zhaoxiran/script2/experiment_reports/20260930T171612Z_seedhr111_stran2_proof_reassessment')
TIMEOUT = 120
SAT_TIMEOUT = 30
AUDIT_SCHEMA = 2
COMMAND = json.loads((OLD / 'joint_baseline/manifest.json').read_text())['command']
ENV = {k: v for k, v in os.environ.items()
       if not k.startswith(('ABC_STRICT_', 'ABC_STRAN_', 'ABC_CEX_', 'ABC_WINDOW_'))}
ENV.update(json.loads((OLD / 'joint_baseline/manifest.json').read_text())['prefix_env'])
ENV.update(ABC_STRAN_PAPER_SKIP_SEQ='0', ABC_STRICT_GUIDE='0')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path = Path(path)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temp.replace(path)


def hdr(path):
    with Path(path).open('rb') as f:
        fields = f.readline().split()
    assert fields[0] == b'aig' and len(fields) == 6, fields
    return list(map(int, fields[1:]))


def graphsha(path):
    data = Path(path).read_bytes()
    m, ni, nl, no, na = hdr(path)
    pos = data.index(b'\n') + 1
    for _ in range(nl + no):
        pos = data.index(b'\n', pos) + 1
    for _ in range(2 * na):
        while data[pos] >= 128:
            pos += 1
        pos += 1
    return hashlib.sha256(data[:pos]).hexdigest()


def audit_graph_chain(directory, commit_numbers):
    """Bind every saved commit to the following snapshot and actual product."""
    directory = Path(directory)
    numbers = sorted(commit_numbers)
    links = []
    previous = None
    for number in numbers:
        before = directory / 'audit' / f'commit-{number:04d}-before.aig'
        after = directory / 'audit' / f'commit-{number:04d}-all.aig'
        before_sha, after_sha = graphsha(before), graphsha(after)
        if previous is not None:
            assert previous['after_graph_sha256'] == before_sha, (
                'commit graph chain mismatch', previous['commit'], number)
        previous = dict(commit=number, before_graph_sha256=before_sha,
                        after_graph_sha256=after_sha)
        links.append(previous)
    final_sha = graphsha(directory / 'final.aig')
    if previous is not None:
        assert previous['after_graph_sha256'] == final_sha, (
            'last committed graph differs from final product', previous['commit'])
    # The first snapshot follows integrated scorr and need not equal input.
    # With no commits, there is no saved post-scorr graph to compare structurally.
    return dict(commits=links, adjacent_links_verified=max(0, len(links) - 1),
                final_link_verified=previous is not None,
                final_graph_sha256=final_sha)


def binary_identity(path):
    path = Path(path).resolve()
    record = json.loads(Path(str(path) + '.build.json').read_text())
    assert record['host'] == socket.gethostname(), (record['host'], socket.gethostname())
    assert record['binary_sha256'] == sha(path), str(path)
    ldd = subprocess.run(['ldd', str(path)], text=True, capture_output=True, check=True)
    assert 'not found' not in ldd.stdout + ldd.stderr
    return dict(path=str(path), sha256=sha(path), build=record, ldd=ldd.stdout)


def runproc(binary, command, log, env, timeout=TIMEOUT):
    log = Path(log)
    start = time.monotonic()
    rc = None
    try:
        with log.open('wb') as stream:
            p = subprocess.run([str(binary), '-q', command], stdout=stream,
                               stderr=subprocess.STDOUT, env=env,
                               cwd=log.parent, timeout=timeout)
        rc = p.returncode
        status = 'exit' if rc == 0 else 'error'
    except subprocess.TimeoutExpired:
        status = 'timeout'
    text = log.read_text(errors='replace')
    if 'Assertion' in text and 'failed' in text:
        status = 'assertion'
    return dict(status=status, returncode=rc, wall_s=time.monotonic() - start,
                timeout_s=timeout, command=command, log=str(log))


def dsec_answer(proof, text):
    """Keep checker failures distinct; only an explicit clean verdict is PASS."""
    if proof['status'] in ('assertion', 'timeout'):
        return proof['status']
    if re.search(r'Networks have different number of (?:primary inputs|primary outputs|latches)'
                 r'|(?:Primary (?:input|output)|Box) #\d+ is different in network', text):
        return 'interface-error'
    if proof['status'] != 'exit':
        return proof['status']
    if 'Both networks have no latches.' in text:
        return 'unsupported'
    if re.search(r'(?:[Mm]iter (?:computation|construction)|Converting miter into AIG'
                 r'|[Tt]he network check) has failed|Cannot (?:open|read)'
                 r'|unknown command|\*\* cmd error|usage: dsec', text):
        return 'checker-error'
    verdicts = set(re.findall(
        r'\bNetworks are (equivalent|NOT EQUIVALENT|not equivalent|NOT equivalent|UNDECIDED)\b', text))
    mapped = {'equivalent': 'pass', 'NOT EQUIVALENT': 'fail',
              'not equivalent': 'fail', 'NOT equivalent': 'fail', 'UNDECIDED': 'undecided'}
    answers = {mapped[v] for v in verdicts}
    if len(answers) == 1:
        return answers.pop()
    if not answers and re.search(r'\b(?:UNDECIDED|UNKNOWN)\b', text):
        return 'undecided'
    return 'parser-error'


def cases():
    rows = []
    for c in json.loads((OLD / 'joint_baseline/manifest.json').read_text())['cases']:
        pre = json.loads((OLD / 'joint_baseline/prefix' / Path(c['file']).stem / 'result.json').read_text())
        assert pre['state'] == 'fixed' and pre['dsec'] == 'pass'
        rows.append(dict(file=c['file'], input=pre['final'], input_sha256=sha(pre['final']),
                         input_graph_sha256=graphsha(pre['final']), loaded=c['loaded'],
                         loaded_sha256=sha(c['loaded']), source_and=int(c['source_and']),
                         input_and=hdr(pre['final'])[4]))
    return rows


def simulate_witness(miter, witness):
    data = Path(miter).read_bytes()
    m, ni, nl, no, na = hdr(miter)
    assert nl == 0 and no == 1
    pos = data.index(b'\n') + 1
    end = data.index(b'\n', pos)
    out = int(data[pos:end])
    pos = end + 1
    bits = Path(witness).read_text().strip()
    assert len(bits) == ni and set(bits) <= {'0', '1'}, (miter, ni, len(bits))
    values = [0] + list(map(int, bits))

    def varint():
        nonlocal pos
        value = shift = 0
        while True:
            byte = data[pos]
            pos += 1
            value |= (byte & 127) << shift
            if byte < 128:
                return value
            shift += 7

    for j in range(na):
        lhs = 2 * (ni + j + 1)
        a = lhs - varint()
        b = a - varint()
        values.append((values[a // 2] ^ (a & 1)) & (values[b // 2] ^ (b & 1)))
    assert len(values) == m + 1 and (values[out // 2] ^ (out & 1)) == 1
    return dict(free_ci_count=ni, output=1, witness_sha256=sha(witness))


def simulate_candidate_witness(before, candidate, witness):
    """Verify the same SAT assignment on the original snapshot and CSV recipe."""
    data = Path(before).read_bytes()
    m, ni, nl, no, na = hdr(before)
    bits = Path(witness).read_text().strip()
    assert len(bits) == ni + nl and set(bits) <= {'0', '1'}
    pos = data.index(b'\n') + 1
    for _ in range(nl + no):
        pos = data.index(b'\n', pos) + 1
    values = [0] + list(map(int, bits))

    def varint():
        nonlocal pos
        value = shift = 0
        while True:
            byte = data[pos]
            pos += 1
            value |= (byte & 127) << shift
            if byte < 128:
                return value
            shift += 7

    for j in range(na):
        lhs = 2 * (ni + nl + j + 1)
        a = lhs - varint()
        b = a - varint()
        values.append((values[a // 2] ^ (a & 1)) & (values[b // 2] ^ (b & 1)))
    assert len(values) == m + 1
    gates = []

    def code_value(code):
        if code >= 0:
            return values[code // 2] ^ (code & 1)
        assert code < -1
        literal = -code - 2
        return gates[literal // 2] ^ (literal & 1)

    recipe = list(map(int, candidate['recipe'].split()))
    assert len(recipe) == 2 * int(candidate['gates'])
    for a, b in zip(recipe[::2], recipe[1::2]):
        gates.append(code_value(a) & code_value(b))
    root_value = values[int(candidate['root'])]
    replacement_value = code_value(int(candidate['out']))
    assert root_value != replacement_value, ('SAT witness does not refute saved candidate', candidate)
    return dict(before_sha256=sha(before), free_ci_count=ni + nl,
                root=int(candidate['root']), root_value=root_value,
                replacement_value=replacement_value, witness_sha256=sha(witness))


def check_miter(checker, miter, before, candidate):
    log, witness = miter.with_suffix('.sat.log'), miter.with_suffix('.cex')
    cmd = f'read_aiger {miter}; sat -C 1000000; write_cex {witness}'
    row = runproc(checker, cmd, log, ENV, SAT_TIMEOUT)
    text = log.read_text(errors='replace')
    answer = 'unknown'
    if row['status'] == 'exit':
        if re.search(r'\bUNSATISFIABLE\b', text):
            answer = 'unsat'
        elif re.search(r'\bSATISFIABLE\b', text):
            answer = 'sat'
    else:
        answer = row['status']
    row.update(miter=str(miter), miter_sha256=sha(miter), answer=answer)
    if answer == 'sat':
        row['independent_replay'] = simulate_witness(miter, witness)
        row['candidate_replay'] = simulate_candidate_witness(before, candidate, witness)
    write_json(miter.with_suffix('.sat.json'), row)
    return row


def commit_phases(log):
    pending, phases, gains = set(), {}, {}
    for line in Path(log).read_text(errors='replace').splitlines():
        if line.startswith('stran-proof-audit:'):
            kv = dict(re.findall(r'([a-z-]+)=([\w.-]+)', line))
            n = int(kv['commit'])
            pending.add(n)
            if kv['subset'] == 'all':
                gains[n] = int(kv['gain'])
        elif line.startswith('stran-root experiment-summary profile:'):
            kv = dict(re.findall(r'([a-z-]+)=([\w.-]+)', line))
            assert sum(gains[n] for n in pending) == int(kv['final-and-gain'])
            for n in pending:
                phases[n] = kv['phase']
            pending.clear()
    assert not pending, pending
    return phases


def audit_case(directory, checker):
    phases = commit_phases(directory / 'transform.log')
    audit = directory / 'audit'
    log_records = {}
    for line in (directory / 'transform.log').read_text(errors='replace').splitlines():
        if line.startswith('stran-proof-audit:'):
            kv = dict(re.findall(r'([a-z-]+)=([\w.-]+)', line))
            log_records.setdefault(int(kv['commit']), {})[kv['subset']] = kv
    csv_paths = sorted(audit.glob('commit-*-candidates.csv'))
    assert {int(p.name.split('-')[1]) for p in csv_paths} == set(phases) == set(log_records)
    graph_chain = audit_graph_chain(directory, phases)
    candidates, commits, sat_rows, unexported_seq_direct = [], [], [], []
    for csv_path in csv_paths:
        n = int(csv_path.name.split('-')[1])
        before = audit / f'commit-{n:04d}-before.aig'
        selected = list(csv.DictReader(csv_path.open()))
        assert len(selected) == int(log_records[n]['all']['selected'])
        assert [int(c['index']) for c in selected] == list(range(len(selected)))
        for subset in ['all', 'direct', 'build', 'cbs-origin', 'scorr-origin']:
            kv = log_records[n][subset]
            assert hdr(audit / f'commit-{n:04d}-{subset}.aig')[4] == int(kv['after'])
            assert hdr(audit / f'commit-{n:04d}-before.aig')[4] == int(kv['before'])
            assert int(kv['before']) - int(kv['after']) == int(kv['gain'])
        flags = []
        for c in selected:
            c = {k: int(v) if k != 'recipe' else v for k, v in c.items()}
            miter = audit / f"commit-{n:04d}-candidate-{c['index']:04d}.aig"
            answer = 'not-requested-direct-cbs'
            if miter.exists():
                sat = check_miter(checker, miter, before, c)
                sat_rows.append(sat)
                answer = sat['answer']
            else:
                assert c['kind'] != 2 and c['origin_lane'] != 2
                if c['certificate_strength'] == 2:
                    answer = 'not-exported-direct-seq-certificate'
                    unexported_seq_direct.append(dict(commit=n, **c))
            c.update(commit=n, phase=phases[n], sat_status=answer)
            if answer == 'sat':
                assert c['certificate_strength'] == 2, ('SAT contradicts combinational certificate', c)
            candidates.append(c)
            flags.append(int(answer == 'sat'))
        all_graph = audit / f'commit-{n:04d}-all.aig'
        direct = audit / f'commit-{n:04d}-direct.aig'
        record = dict(commit=n, phase=phases[n], before_and=hdr(before)[4],
                      after_and=hdr(all_graph)[4],
                      exact_build_gain=hdr(direct)[4] - hdr(all_graph)[4],
                      sat_build_count=sum(f and int(c['kind']) == 2 for c, f in zip(selected, flags)),
                      sat_build_gain=0, sat_all_gain=0)
        if any(flags):
            prefix = audit / f'replay-{n:04d}'
            task = prefix.with_suffix('.task')
            lines = [str(before), str(prefix), str(len(selected))]
            for c, flag in zip(selected, flags):
                lines.append(' '.join([c['root'], c['kind'], c['gates'], c['out'], str(flag),
                                       c['gain'], c['origin_lane'], c['recipe']]))
            task.write_text('\n'.join(lines) + '\n')
            replay = runproc(checker, '&stran_resub_test', prefix.with_suffix('.log'),
                             {**ENV, 'ABC_STRAN_AUDIT_REPLAY': str(task)})
            assert replay['status'] == 'exit', replay
            assert graphsha(str(prefix) + '-all.aig') == graphsha(all_graph)
            record['sat_build_gain'] = hdr(str(prefix) + '-without-sat-build.aig')[4] - hdr(all_graph)[4]
            record['sat_all_gain'] = hdr(str(prefix) + '-without-sat-all.aig')[4] - hdr(all_graph)[4]
            record['replay'] = replay
        commits.append(record)
    result = dict(audit_schema=AUDIT_SCHEMA, audit_script_sha256=sha(__file__),
                  candidates=candidates, commits=commits,
                  graph_chain=graph_chain,
                  unexported_seq_direct=unexported_seq_direct,
                  secondary_complete=not unexported_seq_direct and all(
                      x['answer'] in ('sat', 'unsat') for x in sat_rows),
                  sat_statuses=dict(collections.Counter(x['answer'] for x in sat_rows)),
                  sat_witnesses_verified=sum(x['answer'] == 'sat' for x in sat_rows),
                  complete=all(x['answer'] in ('sat', 'unsat') for x in sat_rows))
    profile = (directory / 'transform.log').read_text(errors='replace')
    initial = int(re.search(r'initial scorr profile:.*?result-and=(\d+)', profile)[1])
    if commits:
        assert commits[0]['before_and'] == initial, 'first commit does not follow initial scorr'
    assert initial - sum(c['before_and'] - c['after_and'] for c in commits) == hdr(directory / 'final.aig')[4]
    for phase in ['comb', 'seq']:
        for kind, number in [('constant', 0), ('existing', 1), ('build', 2)]:
            selected_count = sum(map(int, re.findall(
                r'experiment-commit profile: schema=8 phase=' + phase +
                ' kind=' + kind + r' selected=(\d+)', profile)))
            assert selected_count == sum(c['phase'] == phase and c['kind'] == number for c in candidates)
    for phase in ['comb', 'seq']:
        for key in ['exact_build_gain', 'sat_build_gain', 'sat_all_gain', 'sat_build_count']:
            result[f'{phase}_{key}'] = sum(x[key] for x in commits if x['phase'] == phase)
    write_json(directory / 'audit.json', result)
    return result


def execute(task):
    c, name, arm, checker, out = task
    d = out / name / Path(c['file']).stem
    d.mkdir(parents=True, exist_ok=False)
    (d / 'audit').mkdir()
    env = {**ENV, **arm.get('env', {}), 'ABC_STRAN_AUDIT_DIR': str(d / 'audit')}
    if arm.get('teacher_audit'):
        (d / 'teacher').mkdir()
        env['ABC_STRICT_TEACHER_AUDIT_DIR'] = str(d / 'teacher')
    command = arm.get('command', COMMAND)
    output = d / 'final.aig'
    result = {**c, 'arm': name, 'binary': arm['binary'], 'binary_sha256': sha(arm['binary']),
              'env': {k: v for k, v in env.items() if k.startswith('ABC_')},
              'transform': {'status': 'not-started'},
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        assert sha(c['input']) == c['input_sha256']
        result['transform'] = runproc(arm['binary'], f"&read {c['input']}; {command}; &write {output}",
                                      d / 'transform.log', env)
        write_json(d / 'result.json', result)
        if result['transform']['status'] == 'exit' and output.exists():
            result.update(final_and=hdr(output)[4], final_reg=hdr(output)[2],
                          final_sha256=sha(output), final_graph_sha256=graphsha(output))
            assert sha(c['loaded']) == c['loaded_sha256'], 'loaded baseline changed'
            proof = runproc(checker, f"dsec {c['loaded']} {output}", d / 'dsec.log', ENV)
            text = (d / 'dsec.log').read_text(errors='replace')
            proof['answer'] = dsec_answer(proof, text)
            result['dsec'] = proof
            write_json(d / 'result.json', result)
            audit = audit_case(d, checker)
            result['audit_complete'] = audit['complete']
            result['audit_schema'] = audit['audit_schema']
            result['secondary_complete'] = audit['secondary_complete']
            result['unexported_seq_direct'] = audit['unexported_seq_direct']
            for phase in ['comb', 'seq']:
                for key in ['exact_build_gain', 'sat_build_gain', 'sat_all_gain', 'sat_build_count']:
                    result[f'{phase}_{key}'] = audit[f'{phase}_{key}']
        elif result['transform']['status'] == 'exit':
            result['transform']['status'] = 'missing-output'
    except Exception as error:
        result['analysis_error'] = f'{type(error).__name__}: {error}'
        import traceback
        (d / 'analysis_error.log').write_text(traceback.format_exc())
    write_json(d / 'result.json', result)
    print(name, c['file'], result['transform']['status'], result.get('dsec', {}).get('answer'),
          result.get('seq_sat_build_gain'), result.get('analysis_error', ''), flush=True)
    return result


def summary(out, baseline):
    rows = [json.loads(p.read_text()) for p in out.glob('*/*/result.json')]
    manifest = json.loads((out / 'manifest.json').read_text())
    arms = list(manifest['config']['arms'])
    expected = {c['file'] for c in manifest['cases']}
    valid = lambda r: (r.get('dsec', {}).get('answer') == 'pass' and
                       r.get('audit_complete') and not r.get('analysis_error'))
    eligible = {a: {r['file']: r for r in rows if r['arm'] == a and valid(r)} for a in arms}
    result = dict(baseline=baseline, arms={}, comparisons={})
    for arm in arms:
        rr = [r for r in rows if r['arm'] == arm]
        good = list(eligible[arm].values())
        result['arms'][arm] = dict(planned=len(expected), present=len(rr), valid=len(good),
            missing=sorted(expected - {r['file'] for r in rr}),
            transform_statuses=dict(collections.Counter(r['transform']['status'] for r in rr)),
            dsec_statuses=dict(collections.Counter(r.get('dsec', {}).get('answer', 'not-run') for r in rr)),
            analysis_errors=[r['file'] for r in rr if r.get('analysis_error')],
            incomplete_audit=[r['file'] for r in rr if not r.get('audit_complete')],
            incomplete_secondary=[r['file'] for r in rr if not r.get('secondary_complete')],
            valid_files=sorted(eligible[arm]))
    for arm in arms:
        names = sorted(set(eligible.get(baseline, {})) & set(eligible[arm]))
        if not names:
            continue
        base = [eligible[baseline][n] for n in names]
        cand = [eligible[arm][n] for n in names]
        for b, c in zip(base, cand):
            assert b['input_sha256'] == c['input_sha256'] and b['source_and'] == c['source_and']
            assert b['loaded_sha256'] == c['loaded_sha256'], 'paired loaded baselines differ'
        stats = {}
        for label, rr in [('baseline', base), ('candidate', cand)]:
            values = [100 * r['seq_sat_build_gain'] / r['source_and'] for r in rr]
            stats[label] = dict(true_build_mean_pct=statistics.mean(values),
                true_build_median_pct=statistics.median(values),
                true_build_and=sum(r['seq_sat_build_gain'] for r in rr),
                true_build_weighted_pct=100 * sum(r['seq_sat_build_gain'] for r in rr) / sum(r['source_and'] for r in rr),
                true_build_cases=sum(r['seq_sat_build_gain'] > 0 for r in rr),
                true_build_candidates=sum(r['seq_sat_build_count'] for r in rr),
                all_build_mean_pct=statistics.mean(100 * r['seq_exact_build_gain'] / r['source_and'] for r in rr),
                final_and=sum(r['final_and'] for r in rr),
                instrumented_transform_wall_s=sum(r['transform']['wall_s'] for r in rr))
        delta = [c['seq_sat_build_gain'] - b['seq_sat_build_gain'] for b, c in zip(base, cand)]
        stats.update(paired=len(names), files=names,
                     true_build_better=sum(v > 0 for v in delta),
                     true_build_equal=sum(v == 0 for v in delta),
                     true_build_worse=sum(v < 0 for v in delta),
                     delta_mean_pp=statistics.mean(100 * v / c['source_and'] for v, c in zip(delta, cand)))
        result['comparisons'][arm] = stats
    write_json(out / 'summary.json', result)
    print(json.dumps(result, indent=2))
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--config', type=Path)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--workers', type=int, default=4)
    p.add_argument('--files', nargs='*', help='Explicit pilot subset; omission means Fast35')
    p.add_argument('--baseline', default='control')
    p.add_argument('--analyze', action='store_true')
    p.add_argument('--dry-run', action='store_true')
    args = p.parse_args()
    if args.analyze:
        summary(args.out, args.baseline)
        return
    assert 1 <= args.workers <= 200
    config = json.loads(args.config.read_text())
    cohort = [c for c in cases() if args.files is None or c['file'] in args.files]
    assert cohort
    if args.files is not None:
        assert set(args.files) == {c['file'] for c in cohort}
    identities = None if args.dry_run else {str(b): binary_identity(b) for b in
        {config['checker'], *(a['binary'] for a in config['arms'].values())}}
    plan = dict(host=socket.gethostname(), utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                config=config, binary_identities=identities, cases=cohort, workers=args.workers,
                transform_timeout_s=TIMEOUT, dsec_timeout_s=TIMEOUT, sat_timeout_s=SAT_TIMEOUT,
                script_sha256=sha(__file__), base_command=COMMAND,
                audit_schema=AUDIT_SCHEMA,
                base_env={k: v for k, v in ENV.items() if k.startswith('ABC_')},
                timing_caveat='audit-instrumented; no production speed claim',
                quality='free-state SAT + Python witness replay + full SEQ + exact selected-set Build replay')
    if args.dry_run:
        print(json.dumps(plan, indent=2))
        return
    args.out.mkdir(parents=True, exist_ok=False)
    write_json(args.out / 'manifest.json', plan)
    tasks = [(c, a, config['arms'][a], config['checker'], args.out)
             for c in cohort for a in config['arms']]
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        list(pool.map(execute, tasks))
    summary(args.out, args.baseline)


if __name__ == '__main__':
    main()
