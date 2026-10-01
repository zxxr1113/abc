#!/usr/bin/env python3
"""Bounded matched-grammar Direct audit; never edits the supplied evidence.

Enumerate zero-fresh outputs of the exact signed-pool one/two-AND grammar,
including frozen-hash outputs outside the pool. Only selected roots are audited.
This is an extra-cost attribution check, not a new optimization matrix.
"""
from __future__ import annotations
import argparse
import importlib
import json
from pathlib import Path
import random
import sys
import time
from types import SimpleNamespace


def collect_hash_direct(s, root, pool, max_gates=2, deadline=None):
    """Return direct literal -> one raw grammar witness, with exact frozen hashing.

    A first gate that remains fresh cannot produce a zero-fresh second output:
    the third operand is an old nonconstant pool literal, so it is neither that
    fresh literal nor its complement, and an old hash key requires old operands.
    It is therefore sufficient to extend only first gates folded to old literals.
    All first/second output phases are included. No truth-based hash is used.
    """
    assert max_gates in (1, 2) and len(pool) == len(set(pool))
    assert all(0 < n < root for n in pool)
    literals = [2*n+phase for n in pool for phase in (0, 1)]
    found = {}
    def land(x, y):
        if x == 0 or y == 0 or x == (y ^ 1): return 0
        if x == 1 or x == y: return y
        if y == 1: return x
        old = s.original_hash.get(tuple(sorted((x, y))))
        return 2*old if old is not None and old < root else None
    def record(value, recipe, out):
        if value is not None and value // 2 < root:
            found.setdefault(value, dict(recipe=recipe, out=out))
    for i, x in enumerate(literals):
        if deadline is not None: deadline.remaining()
        for y in literals[i+1:]:
            if x == (y ^ 1): continue
            first = land(x, y)
            if first is None: continue
            for phase in (0, 1): record(first ^ phase, [x,y], -(2+phase))
            if max_gates == 1: continue
            for first_phase in (0, 1):
                for z in literals:
                    value = land(first ^ first_phase, z)
                    if value is None: continue
                    for output_phase in (0, 1):
                        record(value ^ output_phase, [x,y,-(2+first_phase),z], -(4+output_phase))
    return found


def self_test(p):
    """Exact set comparison with brute-force normalize, deterministic fixtures."""
    rng=random.Random(2026100142); fixtures=[]
    fixtures.append((SimpleNamespace(ni=3,nl=0,m=7,na=4,gates=[(2,4),(8,6),(10,2),(12,8)],outputs=[14],latches=[]),7,[1,2,3,4,5]))
    for _ in range(60):
        ni=3;ng=8;gates=[(rng.randrange(2*n),rng.randrange(2*n)) for n in range(ni+1,ni+ng+1)]
        a=SimpleNamespace(ni=ni,nl=0,m=ni+ng,na=ng,gates=gates,outputs=[2*(ni+ng)],latches=[])
        root=rng.randrange(ni+2,a.m+1);pool=sorted(rng.sample(range(1,root),min(root-1,6)));fixtures.append((a,root,pool))
    checked=0
    for a,root,pool in fixtures:
        s=p.Structure(a);lits=[2*n+k for n in pool for k in (0,1)];expected=set()
        for i,x in enumerate(lits):
            for y in lits[i+1:]:
                if x==(y^1):continue
                for op in (0,1):
                    rec,out=p.normalize(s,root,[x,y],-(2+op));checked+=1
                    if not rec:expected.add(out)
                for z in lits:
                    for ip in (0,1):
                        for op in (0,1):
                            rec,out=p.normalize(s,root,[x,y,-(2+ip),z],-(4+op));checked+=1
                            if not rec:expected.add(out)
        actual=collect_hash_direct(s,root,pool)
        assert set(actual)==expected,(root,pool,set(actual)^expected)
        for value,w in actual.items():assert p.normalize(s,root,w['recipe'],w['out'])==([],value)
    assert 12 in collect_hash_direct(p.Structure(fixtures[0][0]),7,fixtures[0][2])
    return dict(status='PASS',seed=2026100142,fixtures=len(fixtures),brute_force_recipes=checked)


def audit(p,product,args):
    start=time.monotonic();deadline=p.Deadline(args.seconds);deadline.start=start;deadline.end=start+args.seconds
    run=args.run.resolve();case=run/args.case;job=json.loads((case/'job.json').read_text());plan=json.loads((run/'plan.json').read_text());selected_dir=args.selection_directory
    if selected_dir is None:selected_dir=Path(json.loads((case/'result.json').read_text())['selected_checkpoint']['directory'])
    selected_dir=selected_dir.resolve();out=args.out.resolve();p.require(not out.exists(),'new output required')
    p.require(not out.is_relative_to(run) and not out.is_relative_to(selected_dir),'output must be outside evidence')
    out.mkdir(parents=True);input_path=Path(job['case']['input']);expected=job['case']['input_sha256'];p.require(p.sha(input_path)==expected,'input hash mismatch')
    sources={str(f):p.sha(f) for f in [input_path,case/'job.json',case/'root_search.jsonl',selected_dir/'selection.json',selected_dir/'product.aig',selected_dir/'product_result.json',run/'plan.json']}
    for name,digest in plan['runtime_source_hashes'].items():p.require(p.sha(run/'source'/name)==digest,'frozen runtime changed')
    solver=args.solver.resolve();p.require(p.sha(solver)==plan['solver_sha256'],'solver mismatch')
    selected=json.loads((selected_dir/'selection.json').read_text())['selected'];a=p.Aiger(input_path);s=p.Structure(a);cfg=p.Config(**job['config']);g,base,step,reset=p.compile_graph(a)
    (free,image,initial),fm=p.signatures(g,[base,step,reset],cfg);sm=(1<<(2*cfg.lanes))-1;seq=[x|(y<<cfg.lanes)for x,y in zip(image,initial)]
    pools={row['root']:row['pool']for row in (json.loads(line)for line in (case/'root_search.jsonl').read_text().splitlines())}
    current=product.rebuild(a,selected);original_and=len(current['gates']);p.require(product.write_aig(out/'original_selection_replay.aig',current)==p.sha(selected_dir/'product.aig'),'selected product replay differs')
    baseline_and=len(product.rebuild(a,[])['gates']);root_rows=[];matches=[];queries=[];order=[]
    for c in selected:
        deadline.remaining();root=c['root'];pool=pools[root];collected=collect_hash_direct(s,root,pool,cfg.max_gates,deadline)
        base_direct={0,1}|{2*n+k for n in set(pool)|p.external_nodes(c['recipe'],c['out'])for k in(0,1)}
        extras=sorted(set(collected)-base_direct);passing=[v for v in extras if seq[v//2]^(sm if v&1 else 0)==seq[root]]
        rejected=[]
        for value in extras:
            deadline.remaining()
            assert p.normalize(s,root,collected[value]['recipe'],collected[value]['out'])==([],value)
            difference=seq[root]^(seq[value//2]^(sm if value&1 else 0))
            if not difference:continue
            packed_lane=(difference&-difference).bit_length()-1;lane=packed_lane%cfg.lanes
            current=[(image[n]>>lane)&1 for n in range(1,1+a.ni)]
            if packed_lane<cfg.lanes:
                previous_inputs=[(free[n]>>lane)&1 for n in range(1,1+a.ni)]
                previous_state=[(free[n]>>lane)&1 for n in range(1+a.ni,1+a.ni+a.nl)]
                successor=a.step(previous_inputs,previous_state)[1]
                sample=dict(domain='unrestricted_one_step_image',reachable_teacher=False,previous_inputs=previous_inputs,previous_state=previous_state)
            else:
                successor=list(a.initial);sample=dict(domain='reset_zero',reachable_teacher=True)
            values=a.step(current,successor)[2];replacement=p.recipe_eval([],value,values)
            assert values[root]!=replacement
            rejected.append(dict(literal=value,packed_signature_lane=packed_lane,current_inputs=current,successor_state=successor,root_value=values[root],direct_value=replacement,replay='PASS',**sample))
        root_rows.append(dict(root=root,pool=pool,build_recipe=c['recipe'],build_out=c['out'],zero_fresh_literals=len(collected),previous_direct_literals=len(base_direct),extra_outside_previous_scope=extras,sample_matching_extras=passing,sample_refutations=rejected,raw_recipe_witnesses={str(v):collected[v]for v in extras}))
        for value in passing:
            assert p.normalize(s,root,collected[value]['recipe'],collected[value]['out'])==([],value)
            cost=s.cost(root,[],value);assert set(cost['removable_nodes'])==s.dereference(root,set()if value<2 else{value//2})
            direct=dict(root=root,recipe=[],out=value,**cost);diff=free[root]^p.recipe_eval([],value,free,fm)
            if diff:
                direct['witness_lane']=(diff&-diff).bit_length()-1;direct['free_witness']=p.witness(a,direct,free)
            rec=dict(root=root,literal=value,raw_grammar_witness=collected[value],direct=direct,build_conservative_gain=c['conservative_gain']);i=len(matches);matches.append(rec)
            for phase,mapping in [('free',base),('reset',reset),('step',step)]:
                miter=g.xor(mapping[root],mapping[value//2]^(value&1));order.append(dict(query=len(queries),alternative=i,root=root,literal=value,phase=phase,miter_literal=miter));queries.append([miter])
    p.write_json(out/'scope.json',root_rows);p.write_json(out/'query_order.json',order)
    if queries:answers,stats=p.run_queries(g,queries,out,solver,deadline)
    else:answers=[];stats=dict(queries=0,statuses={})
    proved=[];cheaper=[]
    for i,rec in enumerate(matches):
        deadline.remaining();codes=answers[3*i:3*i+3];rec['proof']=dict(zip(('free','reset','step'),({-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[v]for v in codes)));rec['sequential_relation_proved']=codes[1:]==[-1,-1]
        if 'free_witness'in rec['direct']:assert codes[0]!=-1
        if not rec['sequential_relation_proved']:continue
        original=next(c for c in selected if c['root']==rec['root']);replacement=[rec['direct'] if c['root']==rec['root']else c for c in selected]
        ands=len(product.rebuild(a,replacement)['gates']);deadline.remaining();rec.update(same_other_selection_and=ands,and_improvement_over_selected_build=original_and-ands,exact_single_direct_gain=baseline_and-len(product.rebuild(a,[rec['direct']])['gates']),exact_single_build_gain=baseline_and-len(product.rebuild(a,[original])['gates']))
        proved.append(rec)
        if ands<original_and:
            cheaper.append(rec);print(json.dumps(dict(event='CHEAPER_DIRECT_FOUND',case=args.case,root=rec['root'],literal=rec['literal'],and_improvement=original_and-ands,proof=rec['proof'])),flush=True)
    deadline.remaining()
    for path,digest in sources.items():p.require(p.sha(path)==digest,'original evidence changed')
    p.require(p.sha(solver)==plan['solver_sha256'],'solver changed');p.write_json(out/'alternatives.json',matches)
    result=dict(status='COMPLETE',case=args.case,selected_roots=len(selected),zero_fresh_literals=sum(r['zero_fresh_literals']for r in root_rows),additional_literals=sum(len(r['extra_outside_previous_scope'])for r in root_rows),additional_matching_literals=len(matches),replayed_sample_refutations=sum(len(r['sample_refutations'])for r in root_rows),proved_extra_directs=len(proved),roots_with_proved_extra_directs=len({r['root']for r in proved}),cheaper_extra_directs=len(cheaper),roots_with_cheaper_extra_directs=len({r['root']for r in cheaper}),unknown_queries=answers.count(0),proof_queries=stats,original_selected_product_and=original_and,source_artifacts_sha256=sources,runtime_source_sha256=plan['runtime_source_hashes'],solver_sha256=plan['solver_sha256'],audit_source_sha256=p.sha(__file__),wall_s=time.monotonic()-start,case_budget_seconds=args.seconds,scope='selected roots only; exact frozen signed-pool connected <=2-AND grammar; only new zero-fresh outputs beyond constants/pool/used-divisor Direct baseline',counterfactual_DSEC='NOT_RUN',original_metric_unchanged=True)
    p.write_json(out/'result.json',result);print(json.dumps(result),flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--case');ap.add_argument('--selection-directory',type=Path);ap.add_argument('--solver',type=Path);ap.add_argument('--out',type=Path);ap.add_argument('--seconds',type=float,default=120);ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    sys.dont_write_bytecode=True;source=args.run.resolve()/'source/nonlinear_divisors';sys.path.insert(0,str(source));p=importlib.import_module('prototype');product=importlib.import_module('product');p.require(Path(p.__file__).resolve()==source/'prototype.py','wrong frozen import')
    if args.self_test:print(json.dumps(self_test(p)));return 0
    p.require(args.seconds>0 and args.case and args.solver and args.out,'case, solver, out, positive seconds required');audit(p,product,args);return 0

if __name__=='__main__':raise SystemExit(main())
