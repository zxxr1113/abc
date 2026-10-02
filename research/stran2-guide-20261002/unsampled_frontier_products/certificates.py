"""Read-only source-certificate replay, derived from reviewed frontier revalidator.
Only the reconstructed CNF destination changes to a NEW audit directory.
Original proof/model files are read-only; no source receipt/path is rewritten.
"""
import csv
import json
from pathlib import Path
from support import *
from proof import validate_model, STATUS
def verify_frontier_receipts(p, a, ia, candidates, source, audit_out, deadline):
    """Replay raw persisted certificates, including full SAT models, without solves."""
    from common import read
    out = Path(source)
    report = read(out/'report.json')
    Bindings(report['bindings']).check(deadline)
    unproved = read(out/'candidates.unproved.json')
    require(candidates == read(out/'candidates.json'), 'passed candidate metadata differs from exact persisted record')
    require(len(candidates) == len(unproved) and all(all(c.get(k) == v for k, v in before.items())
        for c, before in zip(candidates, unproved)), 'unproved candidate identity/cost/metadata changed')
    graph, base, image, reset = p.compile_graph(a)
    miters = [{phase: graph.xor(mapping[c['root']], p.graph_recipe(graph, mapping, c['recipe'], c['out']))
               for phase, mapping in [('free', base), ('reset', reset), ('image', image)]} for c in unproved]
    require(miters == read(out/'miter_literals.json'), 'reconstructed miter literals differ')
    rebuilt = Path(audit_out)/'frontier_source_revalidated.cnf'
    require(not rebuilt.exists(), 'receipt audit output already exists')
    graph.cnf(rebuilt)
    require(sha(rebuilt) == sha(out/'obligations.cnf'), 'reconstructed immutable CNF differs')
    manifests = {}
    for phase in ('free', 'reset', 'image'):
        mp = out/f'{phase}.binding.json'
        m = read(mp)
        require(m['phase'] == phase and m['cnf_sha256'] == sha(rebuilt) and
                m['graph_sha256'] == digest(graph.gates), 'proof phase/graph binding differs')
        require(m['source_binding_sha256'] == sha(m['source_binding_file']), 'source context changed')
        Bindings(read(m['source_binding_file'])).check(deadline)
        require(m['candidates_sha256'] == sha(out/'candidates.unproved.json') and
                m['miter_literals_sha256'] == sha(out/'miter_literals.json'), 'candidate/miter source changed')
        for kind, path in m['paths'].items():
            require(sha(path) == m['hashes'][kind], 'raw proof artifact changed')
        with Path(m['paths']['results']).open() as f:
            rows = list(csv.DictReader(f))
        queries = Path(m['paths']['queries']).read_text().splitlines()
        require(len(rows) == len(m['records']) and int(queries[0]) == len(rows) and len(queries) == len(rows)+1,
                'receipt batch length differs')
        for j, (record, row) in enumerate(zip(m['records'], rows)):
            i = record['candidate_index']
            require(type(i) is int and 0 <= i < len(candidates), 'candidate receipt index out of bounds')
            c = candidates[i]
            require(record == dict(row=j, candidate_index=i, candidate_id=[c['root'], c['recipe'], c['out']],
                assumptions=[miters[i][phase]], result=STATUS[int(row['result'])]), 'manifest record binding differs')
            require(int(row['query']) == j and list(map(int, queries[j+1].split())) == [j, 1, miters[i][phase]],
                    'raw query assumptions/row differ')
            expected = dict(binding_file=str(mp.resolve()), binding_sha256=sha(mp), row=j,
                cnf_sha256=sha(rebuilt), assumptions=[miters[i][phase]], result=record['result'])
            require(c['receipts'].get(phase) == expected and c['proof'][phase] == record['result'],
                    'candidate receipt/status differs from raw batch')
        manifests[phase] = m
    m = manifests['free']
    rows = [json.loads(line) for line in Path(m['paths']['models']).read_text().splitlines()]
    expected_sat = [r['row'] for r in m['records'] if r['result'] == 'SAT']
    require([r['query'] for r in rows] == expected_sat, 'SAT models missing or extraneous')
    for row in rows:
        record = m['records'][row['query']]
        i = record['candidate_index']
        c = candidates[i]
        w = validate_model(graph, m['variables'], row['values'], record['assumptions'], a, ia, base, c)
        w['source_free_receipt'] = c['receipts']['free']
        require(c['free_witness'] == w, 'persisted full SAT witness differs')
        deadline.remaining()
    actual_order = {phase: [r['candidate_index'] for r in m['records']] for phase, m in manifests.items()}
    require(actual_order['free'] == list(range(len(candidates))), 'free batch skipped/reordered a retained candidate')
    require(actual_order['reset'] == [i for i, c in enumerate(candidates) if c['proof']['free'] == 'SAT'],
            'reset phase violated free-first filtering')
    require(actual_order['image'] == [i for i, c in enumerate(candidates)
        if c['proof']['free'] == 'SAT' and c['proof']['reset'] == 'UNSAT'], 'image phase violated reset filtering')
    for c in candidates:
        for phase in ('free', 'reset', 'image'):
            require((phase in c['receipts']) == (c['proof'][phase] != 'NOT_RUN'), 'missing/extra phase receipt')
        good = c['proof'] == dict(free='SAT', reset='UNSAT', image='UNSAT')
        require(c['qualified_offline_opportunity'] == good and
                c['free_witness_replayed'] == (c['proof']['free'] == 'SAT'), 'qualification/replay flag differs')
        require(('free_witness' in c) == (c['proof']['free'] == 'SAT'), 'non-SAT fabricated witness')
    return dict(status='PASS', candidates=len(candidates), full_models=len(rows),
                queries=sum(len(m['records']) for m in manifests.values()), solver_calls=0)
