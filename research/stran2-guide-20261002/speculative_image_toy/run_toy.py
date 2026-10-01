#!/usr/bin/env python3
"""Bounded, standalone regression for image equality versus speculative scorr.

No production imports or edits. Exhaustive checks evaluate a separately decoded
AIG and compare it with direct Boolean transition equations before running ABC.
"""
import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as source:
        for block in iter(lambda: source.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def build_toy():
    gates = []
    e, u, v, q, r, c = (2 * i for i in range(1, 7))

    def land(a, b):
        gates.append((a, b))
        return 2 * (6 + len(gates))

    def mux(s, a, b):
        x, y = land(s, a), land(s ^ 1, b)
        return land(x ^ 1, y ^ 1) ^ 1

    g, uv = land(q, r), land(u, v)
    nexts = [mux(e, u, q), mux(e, v, r), mux(e, uv, g)]
    return dict(ni=3, nl=3, gates=gates, latches=nexts,
                outputs=[c, g], reset=[0, 0, 0])


def write_aig(path, graph):
    ni, nl, gates = graph['ni'], graph['nl'], graph['gates']
    data = bytearray(f'aig {ni + nl + len(gates)} {ni} {nl} {len(graph["outputs"])} {len(gates)}\n'.encode())
    require(graph['reset'] == [0] * nl, 'only zero reset supported')
    for lit in graph['latches'] + graph['outputs']:
        data.extend(f'{lit}\n'.encode())

    def varint(value):
        require(value >= 0, 'non-topological AIG')
        while value >= 128:
            data.append((value & 127) | 128)
            value >>= 7
        data.append(value)

    for node, pair in enumerate(gates, ni + nl + 1):
        hi, lo = sorted(pair, reverse=True)
        require(hi < 2 * node, 'cyclic AIG')
        varint(2 * node - hi)
        varint(hi - lo)
    data.extend(b'c\nspeculative_image_toy; outputs c,g; zero-reset\n')
    Path(path).write_bytes(data)


def read_aig(path):
    data = Path(path).read_bytes()
    pos = 0

    def line():
        nonlocal pos
        end = data.index(b'\n', pos)
        value = data[pos:end]
        pos = end + 1
        return value

    head = line().split()
    require(len(head) == 6 and head[0] == b'aig', 'only ordinary dense binary AIG supported')
    maximum, ni, nl, no, na = map(int, head[1:])
    require(maximum == ni + nl + na, 'not dense')
    latches, reset = [], []
    for _ in range(nl):
        fields = list(map(int, line().split()))
        require(len(fields) in (1, 2), 'bad latch record')
        latches.append(fields[0])
        reset.append(fields[1] if len(fields) == 2 else 0)
    require(reset == [0] * nl, 'nonzero or unknown reset')
    outputs = [int(line()) for _ in range(no)]

    def varint():
        nonlocal pos
        value, shift = 0, 0
        while True:
            byte = data[pos]
            pos += 1
            value |= (byte & 127) << shift
            if byte < 128:
                return value
            shift += 7
            require(shift <= 63, 'oversized varint')

    gates = []
    for node in range(ni + nl + 1, maximum + 1):
        hi = 2 * node - varint()
        lo = hi - varint()
        require(0 <= lo <= hi < 2 * node, 'bad gate')
        gates.append((hi, lo))
    require(all(0 <= x <= 2 * maximum + 1 for x in latches + outputs), 'bad CO literal')
    return dict(ni=ni, nl=nl, gates=gates, latches=latches, outputs=outputs, reset=reset)


def evaluate(graph, state, inputs):
    require(len(inputs) == graph['ni'] and len(state) == graph['nl'], 'input dimension mismatch')
    values = [0] + list(inputs) + list(state)

    def value(lit):
        return values[lit // 2] ^ (lit & 1)

    for a, b in graph['gates']:
        values.append(value(a) & value(b))
    return [value(x) for x in graph['outputs']], [value(x) for x in graph['latches']]


def expected(state, inputs):
    q, r, c = state
    e, u, v = inputs
    return [c, q & r], [u if e else q, v if e else r, (u & v) if e else (q & r)]


def exhaustive(graph):
    require(graph['ni'] == graph['nl'] == 3 and len(graph['outputs']) == 2, 'not the toy interface')
    triples = list(itertools.product((0, 1), repeat=3))
    truth, image, free = [], [], []
    for state, inputs in itertools.product(triples, repeat=2):
        outputs, successor = evaluate(graph, state, inputs)
        require((outputs, successor) == expected(state, inputs), 'AIG differs from equations')
        row = dict(state=list(state), inputs=list(inputs), outputs=outputs, successor=successor)
        truth.append(row)
        if outputs[0] != outputs[1]:
            free.append(row)
        for current in triples:
            image_outputs, _ = evaluate(graph, successor, current)
            require(image_outputs[0] == image_outputs[1], 'image relation false')
            image.append(dict(predecessor_state=list(state), predecessor_inputs=list(inputs),
                              current_inputs=list(current), successor=successor, outputs=image_outputs))
    for inputs in triples:
        outputs, _ = evaluate(graph, (0, 0, 0), inputs)
        require(outputs[0] == outputs[1], 'reset relation false')
    require(free, 'expected free-state inequivalence')
    witness_outputs, witness_next = evaluate(graph, (1, 1, 0), (0, 0, 0))
    require(witness_outputs == [0, 1] and witness_next == [1, 1, 1], 'witness mismatch')
    return dict(status='PASS', transition_rows=len(truth), reset_rows=8,
                image_rows=len(image), free_witnesses=len(free), truth_table=truth,
                image_table=image, free_witness=dict(state=[1, 1, 0], inputs=[0, 0, 0],
                outputs=witness_outputs, successor=witness_next),
                speculative_witness=dict(condition='candidate class {c,g}; representative c',
                    state=[1, 1, 0], inputs=[0, 0, 0], raw_g_frame1=1,
                    speculative_c_frame1=0, original_c_frame1=1,
                    status='ALGEBRAIC_CONDITIONAL_NOT_TRACE'))


def pair_status(graph):
    require(len(graph['outputs']) == 2, 'paired PO interface changed')
    c, g = graph['outputs']
    return dict(c_po_index=0, g_po_index=1, c_literal=c, g_literal=g,
                status='MERGED' if c == g else 'NOT_MERGED')


def dsec_status(process_status, text):
    if process_status != 'EXIT':
        return process_status
    if re.search(r'Networks are equivalent', text):
        return 'PASS'
    if re.search(r'Networks are NOT EQUIVALENT', text, re.I):
        return 'FAIL'
    return 'INCONCLUSIVE'


def command_run(abc, command, logpath, deadline):
    remaining = deadline - time.monotonic()
    require(remaining > 0, 'shared toy deadline exhausted')
    start = time.monotonic()
    with logpath.open('w') as handle:
        process = subprocess.Popen([str(abc), '-c', command], stdout=handle,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=remaining)
            status = 'EXIT' if code == 0 else 'ERROR'
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            code, status = process.returncode, 'TIMEOUT'
    content = logpath.read_text(errors='replace')
    if status == 'EXIT' and re.search(r'Assertion.*failed|(^|\n)(Error:|Cannot open|usage:)', content, re.S):
        status = 'COMMAND_ERROR'
    return dict(command=command, status=status, exit_code=code,
                timeout_seconds=remaining, wall_s=time.monotonic() - start,
                log_sha256=sha(logpath))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--abc', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=30)
    args = parser.parse_args()
    require(0 < args.seconds <= 30, 'toy budget must be at most 30 seconds')
    abc, out = args.abc.resolve(), args.out.resolve()
    require(not out.exists(), 'output directory must not already exist')
    for path in (abc, out):
        require(re.fullmatch(r'[A-Za-z0-9_./+:-]+', str(path)), 'unsupported ABC command path')
    start = time.monotonic()
    deadline = start + args.seconds
    out.mkdir(parents=True)
    source = Path(__file__).resolve()
    repo = source.parents[3]
    tracked_sources = [source, source.with_name('test_toy.py'), repo / 'src/proof/cec/cecCorr.c',
                      repo / 'src/proof/cec/cecClass.c', repo / 'src/proof/cec/cecSeq.c',
                      repo / 'src/proof/cec/cecCore.c', repo / 'src/base/abci/abc.c',
                      repo / 'src/aig/gia/giaCSat.c']
    identities = {str(path.relative_to(repo)): sha(path) for path in tracked_sources}
    abc_hash = sha(abc)
    original, loaded, after = (out / name for name in ('original.aig', 'loaded.aig', 'after.aig'))
    write_aig(original, build_toy())
    proof = exhaustive(read_aig(original))
    write_json(out / 'exhaustive.json', proof)
    command = f'&r {original}; &w {loaded}; &scorr -F 1 -C 1000 -v; &w {after}'
    run = command_run(abc, command, out / 'scorr.log', deadline)
    result = dict(schema=1, abc=str(abc), abc_sha256=abc_hash, source_sha256=identities,
                  shared_budget_seconds=args.seconds, scorr=run,
                  exhaustive={k: v for k, v in proof.items() if k not in ('truth_table', 'image_table')},
                  input_pair=pair_status(read_aig(original)),
                  causal_trace='NOT_CAPTURED', dsec=dict(status='NOT_RUN'))
    if run['status'] == 'EXIT' and after.exists() and loaded.exists():
        exhaustive(read_aig(loaded))
        result['loaded_pair'] = pair_status(read_aig(loaded))
        result['after_pair'] = pair_status(read_aig(after))
        dsec = command_run(abc, f'dsec {original} {after}', out / 'dsec.log', deadline)
        dsec['status'] = dsec_status(dsec['status'], (out / 'dsec.log').read_text())
        result['dsec'] = dsec
    result['files_sha256'] = {p.name: sha(p) for p in out.iterdir() if p.is_file()}
    result['identities_unchanged'] = sha(abc) == abc_hash and all(sha(repo / p) == h for p, h in identities.items())
    require(result['identities_unchanged'], 'source or ABC identity changed during run')
    result['total_wall_s'] = time.monotonic() - start
    write_json(out / 'result.json', result)
    print(json.dumps({key: result.get(key) for key in ('after_pair', 'dsec', 'total_wall_s', 'identities_unchanged')}), flush=True)


if __name__ == '__main__':
    main()
