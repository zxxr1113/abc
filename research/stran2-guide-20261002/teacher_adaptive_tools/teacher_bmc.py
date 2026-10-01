#!/usr/bin/env python3
"""Offline bounded teacher diagnostic; never supplies a SEQ proof or feedback.

Reads first-snapshot exports without changing them. Each SAT trace is replayed
from reset in three independently decoded representations: candidate miter,
snapshot AIGER, and original-ID snapshot CSV plus the saved candidate recipe.
"""
import argparse
import concurrent.futures
import csv
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import tempfile
import time
import traceback

SCHEMA = 1
FRAMES = 64
INNER_TIMEOUT = 110
OUTER_TIMEOUT = 120
CONFLICTS = 1000000


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def artifact(path):
    path = Path(path).resolve()
    return dict(path=str(path), sha256=sha(path), bytes=path.stat().st_size)


def csv_rows(path):
    with Path(path).open(newline='') as stream:
        return list(csv.DictReader(stream))


class Aiger:
    """Dense binary AIGER, preserving latch input and output natural order."""
    def __init__(self, path):
        data = Path(path).read_bytes()
        pos = data.index(b'\n') + 1
        header = data[:pos].split()
        require(len(header) == 6 and header[0] == b'aig', 'unsupported AIGER header')
        self.m, self.ni, self.nl, self.no, self.na = map(int, header[1:])
        require(self.m == self.ni + self.nl + self.na, 'non-dense AIGER')
        self.latches, self.initial, self.outputs, self.gates = [], [], [], []

        def line():
            nonlocal pos
            end = data.index(b'\n', pos)
            result = data[pos:end]
            pos = end + 1
            return result

        for _ in range(self.nl):
            fields = list(map(int, line().split()))
            require(len(fields) in (1, 2), 'invalid latch line')
            self.latches.append(fields[0])
            self.initial.append(fields[1] if len(fields) == 2 else 0)
        require(all(x == 0 for x in self.initial), 'teacher export must have zero reset')
        for _ in range(self.no):
            self.outputs.append(int(line()))

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
                require(shift < 64, 'invalid AIGER varint')

        for index in range(self.na):
            lhs = 2 * (self.ni + self.nl + index + 1)
            first = lhs - varint()
            second = first - varint()
            require(0 <= second <= first < lhs, 'non-topological AIGER gate')
            self.gates.append((first, second))
        require(all(0 <= x <= 2 * self.m + 1 for x in self.latches + self.outputs),
                'AIGER literal out of range')
        self.graph_sha256 = hashlib.sha256(data[:pos]).hexdigest()

    def step(self, inputs, state):
        require(len(inputs) == self.ni and len(state) == self.nl, 'AIGER interface mismatch')
        values = [0] + list(inputs) + list(state)

        def literal(code):
            return values[code // 2] ^ (code & 1)

        for first, second in self.gates:
            values.append(literal(first) & literal(second))
        return ([literal(x) for x in self.outputs],
                [literal(x) for x in self.latches], values)


class SnapshotNodes:
    """Original GIA IDs; CO/buffer IDs are deliberately not AIGER IDs."""
    def __init__(self, path):
        self.nodes = []
        ids = set()
        indexed = {kind: {} for kind in ('pi', 'ro', 'po', 'ri')}
        for row in csv_rows(path):
            node = {key: (value if key == 'kind' else int(value))
                    for key, value in row.items()}
            require(node['id'] not in ids, 'duplicate original node ID')
            require(node['kind'] in ('const', 'pi', 'ro', 'and', 'buf', 'po', 'ri'),
                    'unknown original node kind')
            ids.add(node['id'])
            self.nodes.append(node)
            if node['kind'] in indexed:
                mapping = indexed[node['kind']]
                require(node['index'] not in mapping, 'duplicate interface index')
                mapping[node['index']] = node['id']
        self.nodes.sort(key=lambda node: node['id'])
        require(self.nodes and self.nodes[0]['id'] == 0 and
                self.nodes[0]['kind'] == 'const', 'missing constant zero')
        require(sum(node['kind'] == 'const' for node in self.nodes) == 1,
                'multiple constant nodes')
        self.interfaces = {}
        for kind, mapping in indexed.items():
            require(sorted(mapping) == list(range(len(mapping))), 'non-dense interface indices')
            self.interfaces[kind] = [mapping[x] for x in range(len(mapping))]
        self.ni = len(self.interfaces['pi'])
        self.nl = len(self.interfaces['ro'])
        require(self.nl == len(self.interfaces['ri']), 'RO/RI mismatch')
        seen = {0} | set(self.interfaces['pi']) | set(self.interfaces['ro'])
        for node in self.nodes:
            if node['kind'] in ('and', 'buf', 'po', 'ri'):
                fanins = [node['fanin0']] + ([node['fanin1']] if node['kind'] == 'and' else [])
                require(all(x >= 0 and x // 2 in seen for x in fanins),
                        'original node fanin unavailable')
            seen.add(node['id'])
        self.ids = ids

    def step(self, inputs, state):
        require(len(inputs) == self.ni and len(state) == self.nl, 'snapshot interface mismatch')
        values = {0: 0}
        values.update(zip(self.interfaces['pi'], inputs))
        values.update(zip(self.interfaces['ro'], state))

        def literal(code):
            return values[code // 2] ^ (code & 1)

        for node in self.nodes:
            kind = node['kind']
            if kind == 'and':
                values[node['id']] = literal(node['fanin0']) & literal(node['fanin1'])
            elif kind in ('buf', 'po', 'ri'):
                values[node['id']] = literal(node['fanin0'])
        return ([values[x] for x in self.interfaces['po']],
                [values[x] for x in self.interfaces['ri']], values)


def recipe_value(candidate, values):
    gates = []
    recipe = list(map(int, candidate['recipe'].split()))
    require(len(recipe) == 2 * int(candidate['gates']), 'recipe gate count mismatch')

    def code_value(code):
        if code >= 0:
            require(code // 2 in values, 'external recipe literal unavailable')
            return values[code // 2] ^ (code & 1)
        require(code < -1, 'invalid negative recipe code')
        literal = -code - 2
        require(literal // 2 < len(gates), 'recipe gate not topological')
        return gates[literal // 2] ^ (literal & 1)

    for first, second in zip(recipe[::2], recipe[1::2]):
        gates.append(code_value(first) & code_value(second))
    return code_value(int(candidate['out']))


def parse_status(path):
    """abcLog.c: status depth engine [output] [CEX frame], init, flat trace."""
    lines = Path(path).read_text().splitlines()
    require(len(lines) == 3, 'write_status must have three lines')
    fields = lines[0].split()
    require(len(fields) >= 3 and fields[0] in ('snl_SAT', 'snl_UNSAT', 'snl_UNK'),
            'unknown write_status result')
    result = dict(result=fields[0], bug_free_depth=int(fields[1]), engine=fields[2],
                  initial_bits=lines[1], trace_bits=lines[2])
    if fields[0] == 'snl_SAT':
        require(len(fields) in (4, 5), 'SAT status missing output/frame')
        result.update(output=int(fields[3]),
                      frame=int(fields[4]) if len(fields) == 5 else int(fields[1]))
        require(set(lines[1] + lines[2]) <= {'0', '1'}, 'non-binary status witness')
    else:
        require(len(fields) == 3 and lines[1:] == ['NULL', 'NULL'],
                'unexpected non-SAT witness')
    return result


def parse_cex(path, ni, nl):
    """io.c Abc_NtkDumpOneCex, write_cex -a -t, with unminimized bits."""
    lines = Path(path).read_text().splitlines()
    require(len(lines) >= 5 and lines[0] == '1', 'missing AIGER SAT witness header')
    match = re.fullmatch(r'b(\d+)', lines[1])
    require(match is not None, 'invalid AIGER witness output')
    require(len(lines[2]) == nl and set(lines[2]) <= {'0', '1'}, 'invalid witness reset')
    stop = lines.index('.', 3)
    frames = lines[3:stop]
    require(frames and all(len(bits) == ni and set(bits) <= {'0', '1'} for bits in frames),
            'invalid witness PI frame')
    require(all(line in ('', '# DONE') for line in lines[stop + 1:]), 'extra witness data')
    return dict(output=int(match[1]), initial_bits=lines[2], frames=frames)


def replay_sat(snapshot, nodes, miter, candidate, status, witness):
    require(miter.no == 1 and miter.nl > 0, 'teacher miter must be sequential, single-output')
    require((snapshot.ni, snapshot.nl) == (nodes.ni, nodes.nl) == (miter.ni, miter.nl),
            'miter/snapshot interface differs')
    require(status['output'] == witness['output'] == 0, 'unexpected failing output')
    require(status['initial_bits'] == witness['initial_bits'] == '0' * miter.nl,
            'witness is not from zero reset')
    require(status['trace_bits'] == ''.join(witness['frames']), 'status/CEX traces differ')
    require(status['frame'] == len(witness['frames']) - 1 < FRAMES, 'CEX frame mismatch')
    require(0 <= status['frame'], 'negative CEX frame')
    states = [[0] * graph.nl for graph in (snapshot, nodes, miter)]
    differences = []
    for frame, bits in enumerate(witness['frames']):
        inputs = list(map(int, bits))
        observed = [graph.step(inputs, state)
                    for graph, state in zip((snapshot, nodes, miter), states)]
        original_aig, original_ids, candidate_miter = observed
        require(original_aig[0] == original_ids[0], 'snapshot PO mismatch at frame %d' % frame)
        require(original_aig[1] == original_ids[1] == candidate_miter[1],
                'snapshot/miter transitions differ at frame %d' % frame)
        values = original_ids[2]
        difference = values[int(candidate['root'])] ^ recipe_value(candidate, values)
        require(candidate_miter[0] == [difference], 'recipe/miter mismatch at frame %d' % frame)
        differences.append(difference)
        states = [entry[1] for entry in observed]
    require(differences[-1] == 1, 'SAT trace does not refute original candidate')
    return dict(verified=True, frame_count=len(differences), failing_frame=len(differences) - 1,
                first_failing_frame=differences.index(1), root=int(candidate['root']),
                pi_count=miter.ni, register_count=miter.nl, reset='all_zero',
                miter_outputs=differences, snapshot_aiger_and_original_ids_agree=True,
                snapshot_and_miter_transitions_agree=True)


def classify(process, text, status):
    if re.search(r'Assertion[^\n]*failed|Assertion failed', text):
        return 'assertion'
    if process['state'] == 'timeout':
        return 'outer_timeout'
    if process['returncode'] != 0:
        return 'checker_error'
    if re.search(r'Cannot (?:open|read)|unknown command|\*\* cmd error|usage: '
                 r'|Reading AIGER has failed|Error:|Error reading|The network check has failed', text):
        return 'checker_error'
    if re.search(r'Does not work for combinational networks|only works for', text):
        return 'interface_error'
    if status is None:
        return 'parser_error'
    if status['result'] == 'snl_SAT':
        found = re.findall(r'Output (\d+) of miter .* was asserted in frame (\d+)\.', text)
        if not found or any((int(po), int(frame)) != (status['output'], status['frame'])
                            for po, frame in found):
            return 'parser_error'
        return 'sat_pending_replay'
    if re.search(r'Reached timeout|\(timeout\s+\d+\s+sec\)', text):
        return 'inner_timeout'
    if status['result'] == 'snl_UNSAT':
        return ('proved_state_space' if 'Explored all reachable states' in text
                else 'parser_error')
    completed = [int(x) for x in re.findall(r'^\s*(\d+)\s+\+\s*:', text, re.MULTILINE)]
    if status['bug_free_depth'] == FRAMES - 1 and FRAMES - 1 in completed:
        return 'bounded_safe_64'
    return 'unknown'


def checker_identity(path):
    path = Path(path).resolve()
    build_path = Path(str(path) + '.build.json')
    build = json.loads(build_path.read_text())
    require(build['host'] == socket.gethostname(), 'checker build host differs')
    require(build['binary_sha256'] == sha(path), 'checker binary differs from build record')
    linked = subprocess.run(['ldd', str(path)], text=True, capture_output=True, check=True)
    require('not found' not in linked.stdout + linked.stderr, 'checker dependency missing')
    return dict(binary=artifact(path), build_record=artifact(build_path), build=build,
                ldd_stdout=linked.stdout, ldd_stderr=linked.stderr)


def load_export(path):
    path = Path(path).resolve()
    snapshot_metadata = json.loads((path / 'snapshot.json').read_text())
    require(snapshot_metadata.get('first_snapshot_only') is True,
            'export does not identify the first SEQ snapshot')
    rows = csv_rows(path / 'candidates.csv')
    require(len(rows) <= 32, 'teacher candidate cap exceeded')
    indices = [int(row['index']) for row in rows]
    require(len(indices) == len(set(indices)), 'duplicate candidate index')
    roots_supports = [(int(row['root']), tuple(sorted(map(int, row['support'].split()))))
                      for row in rows]
    require(len(roots_supports) == len(set(roots_supports)), 'duplicate teacher root/support')
    snapshot, nodes = Aiger(path / 'snapshot.aig'), SnapshotNodes(path / 'snapshot-nodes.csv')
    require(snapshot.nl > 0 and (snapshot.ni, snapshot.nl) == (nodes.ni, nodes.nl),
            'export snapshot interface mismatch')
    require((snapshot_metadata.get('pis'), snapshot_metadata.get('registers')) ==
            (snapshot.ni, snapshot.nl), 'snapshot metadata interface mismatch')
    for row in rows:
        require(int(row['gates']) > 0 and int(row['root']) in nodes.ids,
                'candidate is not a Build on the original snapshot')
        require(int(row['seq_completed']) == 1 and int(row['guide_match']) == 1 and
                int(row['raw_check_frames']) == 64 and int(row['reach_mode']) > 0,
                'candidate did not match the 64-frame reset teacher / complete F1 attempt')
        require(int(row['certificate_strength']) == 0,
                'teacher candidate unexpectedly has a proof certificate')
        miter = Aiger(path / ('candidate-%04d-seq.aig' % int(row['index'])))
        require((miter.ni, miter.nl, miter.no) == (snapshot.ni, snapshot.nl, 1),
                'exported candidate miter changed interface')
        # Validate every recipe reference before any checker is launched.
        recipe_value(row, {node_id: 0 for node_id in nodes.ids})
    files = [path / name for name in ('snapshot.aig', 'snapshot-nodes.csv', 'snapshot.json',
                                     'candidates.csv', 'submissions.csv')]
    summary = None
    if (path / 'summary.json').exists():
        files.append(path / 'summary.json')
        summary = json.loads((path / 'summary.json').read_text())
        require(summary.get('selected', len(rows)) == len(rows), 'summary candidate count mismatch')
    files += [path / ('candidate-%04d-seq.aig' % index) for index in indices]
    return dict(path=str(path), candidates=rows, snapshot=snapshot, nodes=nodes,
                artifacts=[artifact(item) for item in files],
                snapshot_metadata=snapshot_metadata, export_summary=summary,
                export_complete=bool(summary and summary.get('complete')))


def diagnose(checker, exported, candidate, output, env):
    output.mkdir()
    miter_path = Path(exported['path']) / ('candidate-%04d-seq.aig' % int(candidate['index']))
    # ABC's command parser receives only local safe basenames. Symlink targets
    # retain the immutable export path and are hashed before and after execution.
    (output / 'miter.aig').symlink_to(miter_path)
    command = ('read_aiger miter.aig; bmc3 -S 0 -F 64 -T 110 -C 1000000 -v; '
               'write_status status.txt; write_cex -a -t witness.cex')
    result = dict(schema=SCHEMA, candidate=candidate, export_path=exported['path'],
                  miter=artifact(miter_path), command=command,
                  argv=[str(checker), '-q', command], cwd=str(output),
                  outer_timeout_s=OUTER_TIMEOUT, inner_timeout_s=INNER_TIMEOUT,
                  frames=FRAMES, conflict_limit=CONFLICTS,
                  diagnostic_only=True, seq_proof=False, algorithm_feedback=True)
    start = time.monotonic()
    try:
        with (output / 'checker.log').open('wb') as stream:
            try:
                child = subprocess.run(result['argv'], cwd=output, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, timeout=OUTER_TIMEOUT)
                process = dict(state='exit', returncode=child.returncode)
            except subprocess.TimeoutExpired:
                process = dict(state='timeout', returncode=None)
        process['wall_s'] = time.monotonic() - start
        result['process'] = process
        text = (output / 'checker.log').read_text(errors='replace')
        status = None
        if (output / 'status.txt').exists():
            try:
                status = parse_status(output / 'status.txt')
                result['status'] = status
            except (ValueError, IndexError) as error:
                result['status_parse_error'] = str(error)
        result['answer'] = classify(process, text, status)
        if result['answer'] == 'sat_pending_replay':
            try:
                miter = Aiger(miter_path)
                witness = parse_cex(output / 'witness.cex', miter.ni, miter.nl)
                result['independent_replay'] = replay_sat(
                    exported['snapshot'], exported['nodes'], miter, candidate, status, witness)
                result['answer'] = 'sat_verified'
            except (ValueError, IndexError, KeyError, OSError) as error:
                result['answer'] = 'replay_error'
                result['replay_error'] = str(error)
        require(sha(miter_path) == result['miter']['sha256'], 'miter changed during BMC')
    except Exception as error:
        result.update(answer='runner_error', error=str(error), traceback=traceback.format_exc())
    result['artifacts'] = [artifact(output / name) for name in
                           ('checker.log', 'status.txt', 'witness.cex') if (output / name).exists()]
    write_json(output / 'result.json', result)
    return result


def write_fixtures(root):
    """Two tiny exports for a separate real-checker contract test by the owner."""
    root = Path(root).resolve()
    root.mkdir()
    for name, nregs, sat in [('sat_frame1', 1, True), ('safe64', 7, False)]:
        path = root / name
        path.mkdir()
        # PI 1; RO 2..nregs+1; root nregs+2 = PI & RO0.
        root_id = nregs + 2
        driver_lines = [2] + [2 * (index + 1) for index in range(1, nregs)]
        prefix = ('aig %d 1 %d 1 1\n' % (root_id, nregs)).encode()
        prefix += ''.join('%d\n' % driver for driver in driver_lines).encode()
        gate_bytes = bytes((2 * root_id - 4, 2))
        (path / 'snapshot.aig').write_bytes(prefix + ('%d\n' % (2 * root_id)).encode() + gate_bytes)
        (path / 'candidate-0000-seq.aig').write_bytes(
            prefix + ('%d\n' % (2 * root_id if sat else 0)).encode() + gate_bytes)
        with (path / 'snapshot-nodes.csv').open('w', newline='') as stream:
            writer = csv.writer(stream)
            writer.writerow(['id', 'kind', 'index', 'fanin0', 'fanin1'])
            writer.writerow([0, 'const', -1, -1, -1])
            writer.writerow([1, 'pi', 0, -1, -1])
            for index in range(nregs):
                writer.writerow([index + 2, 'ro', index, -1, -1])
            writer.writerow([root_id, 'and', -1, 2, 4])
            writer.writerow([root_id + 1, 'po', 0, 2 * root_id, -1])
            for index, driver in enumerate(driver_lines):
                writer.writerow([root_id + 2 + index, 'ri', index, driver, -1])
        candidate = dict(index=0, root=root_id, kind='Build', origin_lane=2,
                         certificate_strength=0, gain=1, gates=1, out=-2,
                         recipe='2 3' if sat else '2 4', support='1 2', batch=0,
                         batch_index=0, submitted_order=0, wave=0, resub_rank=0,
                         seq_completed=1, seq_rounds=1, guide_match=1,
                         raw_check_frames=64, reach_mode=1)
        for filename in ('candidates.csv', 'submissions.csv'):
            with (path / filename).open('w', newline='') as stream:
                writer = csv.DictWriter(stream, list(candidate))
                writer.writeheader()
                writer.writerow(candidate)
        write_json(path / 'summary.json', dict(fixture=True, first_snapshot_only=True,
                                              selected=1, complete=True,
                                              expected='sat_verified' if sat else 'bounded_safe_64'))
        write_json(path / 'snapshot.json', dict(fixture=True, first_snapshot_only=True,
                                               pis=1, registers=nregs))
    return root


def self_test():
    with tempfile.TemporaryDirectory(prefix='stran-teacher-python-') as temporary:
        root = write_fixtures(Path(temporary) / 'exports')
        exported = load_export(root / 'sat_frame1')
        status_path, cex_path = Path(temporary) / 'status', Path(temporary) / 'cex'
        status_path.write_text('snl_SAT 0 unknown 0 1\n0\n11\n')
        cex_path.write_text('1\nb0\n0\n1\n1\n.\n# DONE\n')
        status = parse_status(status_path)
        miter = Aiger(root / 'sat_frame1/candidate-0000-seq.aig')
        witness = parse_cex(cex_path, miter.ni, miter.nl)
        replay = replay_sat(exported['snapshot'], exported['nodes'], miter,
                            exported['candidates'][0], status, witness)
        require(replay['miter_outputs'] == [0, 1], 'sequential fixture replay wrong')
        bad_witness = dict(witness, frames=['0', '0'])
        try:
            replay_sat(exported['snapshot'], exported['nodes'], miter,
                       exported['candidates'][0], status, bad_witness)
        except ValueError:
            pass
        else:
            raise ValueError('corrupt witness accepted')
        exit_process = dict(state='exit', returncode=0)
        unknown = dict(result='snl_UNK', bug_free_depth=63)
        require(classify(exit_process, '  63 + : completed\n', unknown) == 'bounded_safe_64',
                'complete frame cap misclassified')
        require(classify(exit_process, '', unknown) == 'unknown', 'depth alone accepted')
        require(classify(exit_process, 'Reached timeout (110 seconds).', unknown) == 'inner_timeout',
                'inner timeout misclassified')
        require(classify(dict(state='timeout', returncode=None), '', unknown) == 'outer_timeout',
                'outer timeout misclassified')
        safe = load_export(root / 'safe64')
        graph = Aiger(root / 'safe64/candidate-0000-seq.aig')
        states = [[0] * 7 for _ in range(3)]
        for frame in range(64):
            observations = [g.step([frame % 2], s) for g, s in
                            zip((safe['snapshot'], safe['nodes'], graph), states)]
            require(observations[2][0] == [0], 'safe fixture not safe')
            require(observations[0][1] == observations[1][1] == observations[2][1],
                    'fixture transition mismatch')
            states = [row[1] for row in observations]
    return dict(python_self_test='pass', abc_executed=False, schema=SCHEMA)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exports', nargs='+', type=Path,
                        help='one or more export directories, each containing candidates.csv')
    parser.add_argument('--checker', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--validate-only', action='store_true', help='validate exports without ABC')
    parser.add_argument('--self-test', action='store_true', help='pure Python parser/reset tests')
    parser.add_argument('--write-fixtures', type=Path, help='write two exports; do not execute ABC')
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), sort_keys=True))
        return
    if args.write_fixtures:
        print(write_fixtures(args.write_fixtures))
        return
    require(args.exports and 1 <= args.workers <= 8, 'supply exports and workers in 1..8')
    exports = [load_export(path) for path in args.exports]
    require(len({item['path'] for item in exports}) == len(exports), 'duplicate export directory')
    if args.validate_only:
        print(json.dumps(dict(validated=[dict(path=item['path'], candidates=len(item['candidates']))
                                         for item in exports], abc_executed=False), sort_keys=True))
        return
    require(args.checker is not None and args.out is not None, 'supply checker and new out directory')
    checker = args.checker.resolve()
    identity = checker_identity(checker)
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    environment = {key: value for key, value in os.environ.items()
                   if not key.startswith(('ABC_STRICT_', 'ABC_STRAN_', 'ABC_CEX_', 'ABC_WINDOW_'))}
    manifest = dict(schema=SCHEMA, script=artifact(__file__), host=socket.gethostname(),
                    started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    argv=vars(args), checker=identity, workers=args.workers,
                    frames=FRAMES, inner_timeout_s=INNER_TIMEOUT, outer_timeout_s=OUTER_TIMEOUT,
                    conflict_limit=CONFLICTS, diagnostic_only=True, seq_proof=False,
                    environment_policy='remove ABC_STRICT_/ABC_STRAN_/ABC_CEX_/ABC_WINDOW_ prefixes',
                    abc_environment={k: v for k, v in environment.items() if k.startswith('ABC_')},
                    runtime_environment={k: environment.get(k) for k in
                                         ('PATH', 'LD_LIBRARY_PATH', 'OMP_NUM_THREADS',
                                          'MKL_NUM_THREADS', 'OPENBLAS_NUM_THREADS')},
                    exports=[{k: v for k, v in item.items() if k not in ('snapshot', 'nodes')}
                             for item in exports])
    manifest['argv'] = {key: ([str(x) for x in value] if isinstance(value, list)
                             else str(value) if isinstance(value, Path) else value)
                        for key, value in manifest['argv'].items()}
    write_json(output / 'manifest.json', manifest)
    rows = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = []
        for export_index, exported in enumerate(exports):
            for candidate in exported['candidates']:
                directory = output / ('export-%03d-candidate-%04d' %
                                      (export_index, int(candidate['index'])))
                futures.append(executor.submit(diagnose, checker, exported, candidate, directory, environment))
        for future in concurrent.futures.as_completed(futures):
            row = future.result()
            rows.append(row)
            print(json.dumps(dict(export=row['export_path'], candidate=row['candidate']['index'],
                                  answer=row['answer']), sort_keys=True), flush=True)
    rows.sort(key=lambda row: (row['export_path'], int(row['candidate']['index'])))
    counts = {answer: sum(row['answer'] == answer for row in rows)
              for answer in sorted({row['answer'] for row in rows})}
    changed = [item['path'] for exported in exports for item in exported['artifacts']
               if sha(item['path']) != item['sha256']]
    checker_unchanged = sha(checker) == identity['binary']['sha256']
    write_json(output / 'summary.json', dict(schema=SCHEMA, counts=counts, candidates=len(rows),
                                            diagnostic_only=True, seq_proof=False,
                                            exports_changed=changed, checker_unchanged=checker_unchanged,
                                            results=rows,
                                            finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
    require(not changed, 'export artifacts changed while running')
    require(checker_unchanged, 'checker changed while running')
    print(json.dumps(dict(output=str(output), counts=counts), sort_keys=True))


if __name__ == '__main__':
    main()
