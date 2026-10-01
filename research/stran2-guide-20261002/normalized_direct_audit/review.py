#!/usr/bin/env python3
"""Independent, read-only review of the two bounded hash-Direct audits.

Uses inverse raw-edge closure rather than replaying the optimized collector's
operand loops. Writes only this review's new result file; original evidence is
hash checked and never altered. No solver, DSEC, search, or product experiment.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys
import time
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_json(path):
    return json.loads(Path(path).read_text())


def inverse_closure(a, root, pool, max_gates):
    """Classify old raw edges; never call normalize or Structure's hash.

    First operands are distinct, noncomplemented signed nonconstant pool lits.
    A Direct first gate must therefore hit an earlier raw original hash. If it
    misses, the new symbol cannot equal/complement a pool symbol and cannot be
    an operand of an original raw hash. It cannot yield a Direct second gate.
    For reused first gates, second outputs are either a matching old hash or
    the trivial equal/complement rules. Equality is already in the first set;
    complement contributes constants iff the first node is also in the pool.
    """
    allowed = {2*n+p for n in pool for p in (0, 1)}
    canonical = {}
    for node, operands in enumerate(a.gates, a.ni+a.nl+1):
        canonical.setdefault(tuple(sorted(operands)), node)
    nontrivial = {
        key: node for key, node in canonical.items()
        if node < root and 0 not in key and 1 not in key
        and key[0] != key[1] and key[0] != (key[1] ^ 1)
    }
    first = {node for (x,y), node in nontrivial.items()
             if x in allowed and y in allowed}
    answer = {2*n+p for n in first for p in (0, 1)}
    if max_gates == 2:
        if first.intersection(pool):
            answer.update((0, 1))
        extended = {node for (x,y), node in nontrivial.items()
                    if (x//2 in first and y in allowed)
                    or (y//2 in first and x in allowed)}
        answer.update(2*n+p for n in extended for p in (0, 1))
    return answer


def brute(p, a, root, pool, max_gates):
    s = p.Structure(a)
    literals = [2*n+phase for n in pool for phase in (0,1)]
    found, count = set(), 0
    for x,y in itertools.combinations(literals, 2):
        if x == (y ^ 1):
            continue
        for output_phase in (0,1):
            rec,out = p.normalize(s,root,[x,y],-(2+output_phase))
            count += 1
            if not rec:
                found.add(out)
        if max_gates == 2:
            for z,inner_phase,output_phase in itertools.product(literals,(0,1),(0,1)):
                rec,out = p.normalize(s,root,[x,y,-(2+inner_phase),z],-(4+output_phase))
                count += 1
                if not rec:
                    found.add(out)
    return found,count


def fixtures(p, collector):
    def graph(gates):
        return SimpleNamespace(ni=2,nl=0,m=2+len(gates),na=len(gates),
                               gates=gates,outputs=[2*(2+len(gates))],latches=[])
    # Includes duplicate hashes, self/future-only hash hits, complemented inner
    # output, retained first gate in pool, and degenerate original raw nodes.
    examples = [
        (graph([(2,4),(6,2),(8,4),(10,2)]),6,[1,2]),
        (graph([(2,4),(7,2),(8,4),(10,2)]),6,[1,2]),
        (graph([(2,4),(6,2),(8,4),(10,2)]),6,[1,2,3]),
        (graph([(2,4),(2,4),(6,2),(8,2)]),6,[1,2,3]),
        (graph([(2,2),(2,3),(0,4),(1,4),(2,4),(8,6)]),8,[1,2,3,4]),
        (graph([(2,4),(6,2),(2,5),(10,2)]),3,[1,2]),
        (graph([(2,2),(2,4),(8,2),(10,2)]),4,[1,2]),
    ]
    rng = random.Random(2026100153)
    for _ in range(80):
        a = graph([(rng.randrange(2*n),rng.randrange(2*n)) for n in range(3,10)])
        root = rng.randrange(3,a.m+1)
        pool = rng.sample(range(1,root),min(root-1,rng.randrange(2,6)))
        examples.append((a,root,pool))
    total = 0
    boundary_coverage = {"self_hash_excluded":False,"future_hash_excluded":False,
                         "constant_collapse":False,"outside_pool_hash":False}
    for a,root,pool in examples:
        for budget in (1,2):
            expected,count = brute(p,a,root,pool,budget)
            actual = set(collector(p.Structure(a),root,pool,budget))
            inverse = inverse_closure(a,root,pool,budget)
            assert expected == actual == inverse,(root,pool,budget,expected,actual,inverse)
            assert all(v//2 < root for v in actual)
            total += count
            boundary_coverage['constant_collapse'] |= bool(actual.intersection((0,1)))
            boundary_coverage['outside_pool_hash'] |= any(v>=2 and v//2 not in pool for v in actual)
        raw = p.Structure(a).original_hash
        signed = {2*n+phase for n in pool for phase in (0,1)}
        for (x,y),node in raw.items():
            if x in signed and y in signed and x!=y and x!=(y^1):
                boundary_coverage['self_hash_excluded'] |= node == root
                boundary_coverage['future_hash_excluded'] |= node > root
    assert all(boundary_coverage.values()), boundary_coverage
    return dict(fixtures=len(examples),gate_budgets=[1,2],brute_force_recipes=total,
                seed=2026100153,status='PASS',boundary_coverage=boundary_coverage)


def read_raw_aiger(path):
    """Separate binary AIGER decoder, independent of runtime Aiger.step."""
    data=Path(path).read_bytes();pos=data.index(b'\n')+1
    head=data[:pos].decode().split()
    assert head[0]=='aig' and len(head)==6
    m,ni,nl,no,na=map(int,head[1:]);assert m==ni+nl+na
    def line():
        nonlocal pos
        end=data.index(b'\n',pos);v=data[pos:end];pos=end+1;return v
    latches=[]
    for _ in range(nl):
        row=list(map(int,line().split()));assert len(row)==1 or row[1]==0
        latches.append(row[0])
    outputs=[int(line()) for _ in range(no)]
    def varint():
        nonlocal pos
        out=shift=0
        while True:
            b=data[pos];pos+=1;out|=(b&127)<<shift
            if b<128:return out
            shift+=7
    gates=[]
    for n in range(ni+nl+1,m+1):
        x=2*n-varint();y=x-varint();assert 0<=y<=x<2*n
        gates.append((x,y))
    return SimpleNamespace(m=m,ni=ni,nl=nl,na=na,gates=gates,
                           outputs=outputs,latches=latches)


def evaluate(a,inputs,state):
    assert len(inputs)==a.ni and len(state)==a.nl
    values=[0]+inputs+state
    assert all(v in (0,1) for v in values)
    for x,y in a.gates:
        values.append((values[x//2]^(x&1)) & (values[y//2]^(y&1)))
    next_state=[values[v//2]^(v&1) for v in a.latches]
    return values,next_state


def review_case(p,collector,directory):
    directory=Path(directory);result=load_json(directory/'result.json')
    files={str(f):digest(f) for f in directory.iterdir() if f.is_file()}
    for path,expected in result['source_artifacts_sha256'].items():
        assert digest(path)==expected, path
    paths=list(result['source_artifacts_sha256'])
    input_path=next(path for path in paths if '/inputs/first_seq/' in path)
    selection_path=next(path for path in paths if path.endswith('/selection.json'))
    selected={c['root']:c for c in load_json(selection_path)['selected']}
    root_log=next(path for path in paths if path.endswith('/root_search.jsonl'))
    pools={c['root']:c['pool'] for c in map(json.loads,Path(root_log).read_text().splitlines())}
    a=read_raw_aiger(input_path)
    s=p.Structure(a)
    rows=load_json(directory/'scope.json')
    assert {r['root'] for r in rows}==set(selected)
    added=total=refuted=0;domains={}
    for row in rows:
        root=row['root'];pool=row['pool'];assert pool==pools[root]
        c=selected[root];assert (c['recipe'],c['out'])==(row['build_recipe'],row['build_out'])
        computed=inverse_closure(a,root,pool,2)
        assert computed==set(collector(s,root,pool,2))
        assert len(computed)==row['zero_fresh_literals']
        used={v//2 for v in c['recipe']+[c['out']] if v>=2}
        baseline={0,1}|{2*n+phase for n in set(pool)|used for phase in (0,1)}
        extras=computed-baseline
        assert extras==set(row['extra_outside_previous_scope'])
        assert set(row['sample_matching_extras'])==set()
        assert {r['literal'] for r in row['sample_refutations']}==extras
        for literal,raw in row['raw_recipe_witnesses'].items():
            assert p.normalize(s,root,raw['recipe'],raw['out'])==([],int(literal))
        for ref in row['sample_refutations']:
            if ref['domain']=='unrestricted_one_step_image':
                assert ref['reachable_teacher'] is False
                _,state=evaluate(a,ref['previous_inputs'],ref['previous_state'])
            else:
                assert ref['domain']=='reset_zero' and ref['reachable_teacher'] is True
                state=[0]*a.nl
            assert state==ref['successor_state']
            values,_=evaluate(a,ref['current_inputs'],state)
            value=values[ref['literal']//2]^(ref['literal']&1)
            assert (values[root],value)==(ref['root_value'],ref['direct_value'])
            assert values[root]!=value
            domains[ref['domain']]=domains.get(ref['domain'],0)+1
            refuted+=1
        total+=len(computed);added+=len(extras)
    assert total==result['zero_fresh_literals'] and added==result['additional_literals']
    assert refuted==result['replayed_sample_refutations']==added
    assert result['proof_queries']['queries']==result['additional_matching_literals']==0
    assert load_json(directory/'alternatives.json')==load_json(directory/'query_order.json')==[]
    for path,expected in files.items():assert digest(path)==expected
    for path,expected in result['source_artifacts_sha256'].items():assert digest(path)==expected
    return dict(case=result['case'],selected_roots=len(rows),exact_zero_fresh_literals=total,
                additional_literals=added,independent_raw_refutations=refuted,domains=domains,
                inverse_closure_matches_collector=True,formal_queries=0,
                audit_artifacts_sha256=files,status='PASS')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();assert not args.out.exists()
    start=time.monotonic()
    sys.path.insert(0,'/tmp/nonlinear-anytime-pilot-v2/source/nonlinear_divisors')
    import prototype as p
    script=HERE.parent/'nonlinear_divisors/hash_direct_audit.py'
    spec=importlib.util.spec_from_file_location('reviewed_hash_direct_audit',script)
    audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
    source_hash=digest(script)
    result=dict(status='PASS',fixture_tests=fixtures(p,audit.collect_hash_direct),
                cases=[review_case(p,audit.collect_hash_direct,d) for d in
                       ('/tmp/hash-direct-b20-v2','/tmp/hash-direct-cegar-wb-v2')],
                reviewed_collector_sha256=source_hash,review_source_sha256=digest(__file__),
                no_runtime_or_existing_evidence_edits=True,
                completeness='Exact frozen signed-pool nondegenerate first-AND and connected second-AND grammar, both phases, old IDs below root; not full-graph or semantic equivalence closure',
                interpretation='All 248 extras fail unrestricted-image sufficiency by independent replay. This does not prove reachable-state inequivalence.',
                unexercised='Formal proof and exact counterfactual cost branches are not reached because no extra passes signatures.',
                findings=[])
    assert digest(script)==source_hash
    result['wall_s']=time.monotonic()-start
    args.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='cases'}))


if __name__=='__main__':main()
