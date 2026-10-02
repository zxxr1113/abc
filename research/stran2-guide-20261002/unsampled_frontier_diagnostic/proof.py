"""Candidate-local full free SAT witnesses and isolated frozen proof receipts."""
from __future__ import annotations
import copy
import csv
import json
from pathlib import Path
import subprocess
import time
from common import Bindings, cid, digest, require, sha, write_new
from independent_aig import recipe as independent_recipe
STATUS = {-1: 'UNSAT', 0: 'UNKNOWN', 1: 'SAT'}

def validate_model(graph, variables, bits, assumptions, a, ia, base, candidate):
    expected = [i for i, gate in enumerate(graph.gates) if i and gate is None]
    require(variables == expected and len(bits) == len(expected), 'incomplete/reordered graph PI schema')
    require(all(type(v) is int and v in (0, 1) for v in bits), 'non-Boolean full PI model')
    assignments = dict(zip(variables, bits))
    values = [0]
    for node, gate in enumerate(graph.gates[1:], 1):
        if gate is None:
            values.append(assignments[node])
        else:
            x, y = gate
            require(x//2 < node and y//2 < node, 'non-DAG compiled graph')
            values.append((values[x//2] ^ (x&1)) & (values[y//2] ^ (y&1)))
    require(all(values[lit//2] ^ (lit&1) for lit in assumptions), 'model violates exact assumptions')
    ci = [values[lit//2] ^ (lit&1) for lit in base[1:a.ni+a.nl+1]]
    inputs, state = ci[:a.ni], ci[a.ni:]
    original = a.step(inputs, state)[2]
    independent = ia.values(inputs, state)
    require(original == independent, 'full original-AIG replay implementations disagree')
    # Check every original node, not only the miter cone.
    require(original == [values[x//2] ^ (x&1) for x in base], 'compiled free mapping differs from original graph')
    old = independent[candidate['root']]
    new = independent_recipe(candidate['recipe'], candidate['out'], independent)
    require(old != new, 'free SAT model fails original root/recipe difference')
    return dict(kind='candidate_local_free_SAT', inputs=inputs, state=state,
                root=old, replacement=new, replay='PASS', global_lane=None,
                reachable_teacher=False, complete_graph_pi_projection=True)

class Broker:
    def __init__(self, graph, out, solver, deadline, source_binding):
        self.graph, self.out = graph, Path(out)
        self.out.mkdir()
        self.solver, self.deadline = Path(solver), deadline
        self.bound = Bindings(source_binding)
        self.bound.add(self.solver)
        self.context = self.out/'source_bindings.json'
        write_new(self.context, self.bound.files)
        self.bound.add(self.context)
        self.cnf = self.out/'obligations.cnf'
        graph.cnf(self.cnf)
        self.bound.add(self.cnf)
        self.cnf_hash = sha(self.cnf)
        self.variables = [i for i, gate in enumerate(graph.gates) if i and gate is None]
        self.graph_identity = digest(graph.gates)
        self.reports = []
    def batch(self, phase, indexes, miters, candidates):
        require(phase in ('free', 'reset', 'image'), 'invalid proof phase')
        require(len(indexes) == len(set(indexes)), 'duplicate query candidate')
        self.deadline.remaining()
        require(digest(self.graph.gates) == self.graph_identity, 'compiled graph changed')
        # Bound every source and immutable output before and after each solve.
        self.bound.check(self.deadline)
        qpath = self.out/f'{phase}.queries'
        rpath = self.out/f'{phase}.results.csv'
        queries = [[miters[i][phase]] for i in indexes]
        with qpath.open('x') as f:
            f.write(str(len(queries))+'\n')
            for j, query in enumerate(queries):
                f.write(f'{j} {len(query)} '+' '.join(map(str, query))+'\n')
        self.bound.add(qpath)
        paths = dict(cnf=self.cnf, queries=qpath, results=rpath)
        command = [str(self.solver), str(self.cnf), str(qpath), str(rpath)]
        if phase == 'free':
            vpath, mpath = self.out/'free.projection', self.out/'free.models.jsonl'
            with vpath.open('x') as f:
                f.write(f'free {len(self.variables)}\n'+' '.join(map(str, self.variables))+'\n')
            self.bound.add(vpath)
            paths.update(projection=vpath, models=mpath)
            command += [str(vpath), str(mpath)]
        started = time.monotonic()
        if indexes:
            with (self.out/f'{phase}.solver.log').open('x') as log:
                process = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT,
                                         timeout=self.deadline.remaining(), check=False)
            require(process.returncode == 0, f'{phase} solver exit {process.returncode}')
        else:
            with rpath.open('x') as f:
                f.write('query,result,conflicts,wall_s\n')
            if phase == 'free':
                with mpath.open('x'):
                    pass
        process_wall = time.monotonic()-started
        self.deadline.remaining()
        self.bound.check(self.deadline)
        with rpath.open() as f:
            rows = list(csv.DictReader(f))
        require([int(r['query']) for r in rows] == list(range(len(indexes))), 'incomplete/reordered result rows')
        answers = [int(r['result']) for r in rows]
        require(all(x in STATUS for x in answers), 'invalid status')
        require(all(int(r['conflicts']) >= 0 and float(r['wall_s']) >= 0 for r in rows), 'invalid solver work receipt')
        models = {}
        if phase == 'free':
            raw = [json.loads(line) for line in mpath.read_text().splitlines()]
            require(all(set(r) == {'query', 'values'} and type(r['query']) is int for r in raw), 'malformed model record')
            require([r['query'] for r in raw] == [i for i, v in enumerate(answers) if v == 1],
                    'missing/extra/reordered SAT models')
            for r in raw:
                require(len(r['values']) == len(self.variables) and
                        all(type(b) is int and b in (0, 1) for b in r['values']), 'incomplete full model')
            models = {indexes[r['query']]: r['values'] for r in raw}
        for path in paths.values():
            self.bound.add(path)
        manifest = dict(schema=1, phase=phase, cnf_sha256=self.cnf_hash,
                        solver_sha256=sha(self.solver), graph_sha256=self.graph_identity,
                        source_binding_file=str(self.context.resolve()), source_binding_sha256=sha(self.context),
                        candidates_sha256=sha(self.out/'candidates.unproved.json'),
                        miter_literals_sha256=sha(self.out/'miter_literals.json'),
                        variables=self.variables if phase == 'free' else [],
                        paths={k: str(v.resolve()) for k, v in paths.items()},
                        hashes={k: sha(v) for k, v in paths.items()},
                        records=[dict(row=j, candidate_index=i, candidate_id=[cid(candidates[i])[0],
                            list(cid(candidates[i])[1]), cid(candidates[i])[2]],
                            assumptions=queries[j], result=STATUS[answers[j]]) for j, i in enumerate(indexes)])
        mp = self.out/f'{phase}.binding.json'
        write_new(mp, manifest)
        self.bound.add(mp)
        receipts = {i: dict(binding_file=str(mp.resolve()), binding_sha256=sha(mp), row=j,
                           cnf_sha256=self.cnf_hash, assumptions=queries[j], result=STATUS[answers[j]])
                    for j, i in enumerate(indexes)}
        self.reports.append(dict(phase=phase, queries=len(indexes), process_wall_s=process_wall,
                                 solver_wall_s=sum(float(r['wall_s']) for r in rows),
                                 conflicts=sum(int(r['conflicts']) for r in rows),
                                 statuses={STATUS[x]: answers.count(x) for x in STATUS}))
        return dict(zip(indexes, answers)), models, receipts

def prove(p, a, ia, candidates, solver, out, deadline, source_binding):
    require(len(candidates) <= 256 and len({cid(c) for c in candidates}) == len(candidates),
            'extra candidate/free query cap or duplicate violated')
    candidates = copy.deepcopy(candidates)
    graph, base, image, reset = p.compile_graph(a)
    miters = []
    for c in candidates:
        require('witness_lane' not in c and 'free_witness' not in c, 'unsampled candidate has fabricated witness')
        deadline.remaining()
        miters.append({phase: graph.xor(mapping[c['root']], p.graph_recipe(graph, mapping, c['recipe'], c['out']))
                       for phase, mapping in [('free', base), ('reset', reset), ('image', image)]})
    broker = Broker(graph, out, solver, deadline, source_binding)
    write_new(Path(out)/'candidates.unproved.json', candidates)
    write_new(Path(out)/'miter_literals.json', miters)
    broker.bound.add(Path(out)/'candidates.unproved.json')
    broker.bound.add(Path(out)/'miter_literals.json')
    records = [dict(free='NOT_RUN', reset='NOT_RUN', image='NOT_RUN') for _ in candidates]
    receipts = [{} for _ in candidates]
    answers, models, bound = broker.batch('free', list(range(len(candidates))), miters, candidates)
    replay_start = time.monotonic()
    free_sat = []
    for i, answer in answers.items():
        records[i]['free'], receipts[i]['free'] = STATUS[answer], bound[i]
        if answer == 1:
            witness = validate_model(graph, broker.variables, models[i], [miters[i]['free']],
                                     a, ia, base, candidates[i])
            witness['source_free_receipt'] = bound[i]
            candidates[i]['free_witness'] = witness
            free_sat.append(i)
        deadline.remaining()
    replay_wall = time.monotonic()-replay_start
    reset_answers, _, bound = broker.batch('reset', free_sat, miters, candidates)
    reset_safe = []
    for i, answer in reset_answers.items():
        records[i]['reset'], receipts[i]['reset'] = STATUS[answer], bound[i]
        if answer == -1:
            reset_safe.append(i)
    image_answers, _, bound = broker.batch('image', reset_safe, miters, candidates)
    for i, answer in image_answers.items():
        records[i]['image'], receipts[i]['image'] = STATUS[answer], bound[i]
    for i, c in enumerate(candidates):
        c['proof'] = records[i]
        c['qualified_offline_opportunity'] = records[i] == dict(free='SAT', reset='UNSAT', image='UNSAT')
        c['receipts'] = receipts[i]
        c['attempted_identity'] = [cid(c)[0], list(cid(c)[1]), cid(c)[2]]
        c['free_witness_replayed'] = 'free_witness' in c
        c['main_metric_eligible'] = False
        c['native_recipe_novelty'] = 'NOT_CHECKED'
    broker.bound.check(deadline)
    write_new(Path(out)/'candidates.json', candidates)
    broker.bound.add(Path(out)/'candidates.json')
    report = dict(candidate_count=len(candidates), free_queries=len(candidates),
                  total_queries=sum(r['queries'] for r in broker.reports),
                  qualified=sum(c['qualified_offline_opportunity'] for c in candidates),
                  model_replay_wall_s=replay_wall, phases=broker.reports,
                  conflicts_per_query=1000, backfill=False, global_free_additions=0,
                  bindings=broker.bound.files)
    write_new(Path(out)/'report.json', report)
    deadline.remaining()
    return candidates, report

def revalidate_receipts(p, a, ia, candidates, out, deadline):
    """Replay raw persisted certificates, including full SAT models, without solves."""
    from common import read
    out = Path(out)
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
    rebuilt = out/'revalidated.cnf'
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
