#!/usr/bin/env python3
"""Fixed first-chunk image-domain counterexample diagnostic, never a teacher.

Imports the baseline's frozen implementation. Does not alter the production or
anytime lanes, pools, root ordering, free signatures, or acceptance proof class.
"""
from __future__ import annotations
import argparse
from collections import Counter
import copy
import csv
import hashlib
import importlib
import json
from pathlib import Path
import random
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path = Path(path)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def load_runtime(source):
    source = Path(source).resolve()
    sys.path.insert(0, str(source / "nonlinear_divisors"))
    module = importlib.import_module("prototype")
    require(Path(module.__file__).resolve() == source / "nonlinear_divisors/prototype.py",
            "runtime module already loaded from different source")
    return module


def candidate_id(c):
    return (c["root"], tuple(c["recipe"]), c["out"])


def verify_source(p, run, source, job, old, graph, mappings, out, solver):
    plan=json.loads((run/"plan.json").read_text())
    require(json.loads((run/"source_integrity.json").read_text())["status"]=="PASS", "source integrity was not PASS")
    require(job["source_hashes"]==plan["runtime_source_hashes"],"job/runtime identity differs from frozen plan")
    bound={run/"source"/name:value for name,value in plan["runtime_source_hashes"].items()}
    bound[Path(solver)]=plan["solver_sha256"]
    for path,expected in bound.items(): require(sha(path)==expected,"frozen runtime/solver changed")
    chunk=source/"chunks/chunk_00000"
    rebuilt=p.Graph();rebuilt.gates=list(graph.gates);rebuilt.hash=dict(graph.hash)
    literals=[]
    for c in old:
        row={}
        for phase,mapping in mappings.items():
            new=p.graph_recipe(rebuilt,mapping,c["recipe"],c["out"])
            row[phase]=rebuilt.xor(mapping[c["root"]],new)
        literals.append(row)
    replay=out/"source_rebuilt.cnf";rebuilt.cnf(replay)
    require(sha(replay)==sha(chunk/"obligations.cnf"),"source proof CNF did not independently reproduce")
    require(literals==json.loads((chunk/"query_literals.json").read_text()),"source literal map mismatch")
    bound[chunk/"obligations.cnf"]=sha(replay)
    cached={}
    for index,c in enumerate(old):
        cert=c["anytime_certificate"];proof=c["proof"]
        require(cert["input_sha256"]==job["case"]["input_sha256"] and cert["candidate_index"]==index and
                cert["chunk"]=="chunk_00000" and cert["root"]==c["root"] and cert["recipe"]==c["recipe"] and
                cert["out"]==c["out"] and cert["miter_literals"]==literals[index] and
                cert["cnf_sha256"]==sha(replay),"source certificate identity mismatch")
        for phase in ("free","reset","step"):
            if proof[phase]=="NOT_RUN":
                require(phase not in cert["receipts"],"NOT_RUN has proof receipt")
                continue
            receipt=cert["receipts"][phase]
            require(receipt["cnf_sha256"]==cert["cnf_sha256"] and receipt["assumptions"]==[literals[index][phase]] and
                    receipt["result"]==proof[phase],"source proof receipt mismatch")
            paths={}
            for kind in ("queries","results"):
                name=receipt[kind+"_file"]
                require(Path(name).name==name and name not in (".",".."),"invalid source receipt path")
                path=chunk/name;paths[kind]=path
                if path not in bound: bound[path]=sha(path)
                require(bound[path]==receipt[kind+"_sha256"],"source receipt hash mismatch")
                if path not in cached:
                    if kind=="queries":
                        lines=path.read_text().splitlines();require(len(lines)==int(lines[0])+1,"incomplete source queries")
                        cached[path]=[list(map(int,line.split())) for line in lines[1:]]
                    else: cached[path]=list(csv.DictReader(path.open()))
            row=receipt["row"]
            query,answer=cached[paths["queries"]][row],cached[paths["results"]][row]
            require(query==[row,1,literals[index][phase]] and int(answer["query"])==row and
                    {-1:"UNSAT",0:"UNKNOWN",1:"SAT"}[int(answer["result"])]==proof[phase],"source raw answer mismatch")
        good=(proof["free"],proof["reset"],proof["step"])==("SAT","UNSAT","UNSAT")
        require(c["qualified_offline_opportunity"]==good,"source qualification flag mismatch")
    return bound


def projected_pis(graph, base, step, a):
    """Explicit predecessor u/s and independent current x; no guessed indices."""
    roles = dict(previous_inputs=base[1:1+a.ni],
                 previous_state=base[1+a.ni:1+a.ni+a.nl],
                 current_inputs=step[1:1+a.ni])
    literals = sum(roles.values(), [])
    require(all(lit >= 2 and not lit & 1 and graph.gates[lit//2] is None for lit in literals),
            "frame source must be an uncomplemented graph PI")
    require(len(set(literals)) == len(literals), "state/input/frame variables not independent")
    variables = [lit//2 for lit in literals]
    require(set(variables) == {i for i,g in enumerate(graph.gates) if i and g is None},
            "projection does not cover all graph PIs")
    return roles, variables


def graph_values(graph, variables, bits):
    require(len(variables) == len(bits) and all(type(x) is int and x in (0,1) for x in bits),
            "incomplete/non-Boolean PI model")
    assignment = dict(zip(variables, bits))
    require(len(assignment) == len(variables), "duplicate variable projection")
    values = [0]
    for i, gate in enumerate(graph.gates[1:], 1):
        if gate is None:
            require(i in assignment, "missing graph PI")
            values.append(assignment[i])
        else:
            x,y = gate
            values.append((values[x//2] ^ (x&1)) & (values[y//2] ^ (y&1)))
    return values


def replay_model(a, graph, roles, variables, bits, candidate, miter, phase, recipe_eval):
    """Check formal-assumption and original-AIG replay independently."""
    require(phase in ("image", "reset"), "free/unproven domains cannot teach this search")
    compiled = graph_values(graph, variables, bits)
    require((compiled[miter//2] ^ (miter&1)) == 1, "SAT model violates source miter")
    assignment = dict(zip(variables,bits))
    read = lambda role: [assignment[lit//2] ^ (lit&1) for lit in roles[role]]
    u,s,x = read("previous_inputs"),read("previous_state"),read("current_inputs")
    successor = a.step(u,s)[1] if phase == "image" else list(a.initial)
    values = a.step(x,successor)[2]
    old = values[candidate["root"]]
    new = recipe_eval(candidate["recipe"],candidate["out"],values)
    require(old != new, "SAT model fails independent original-AIG recipe replay")
    return dict(domain="unrestricted_one_step_image" if phase == "image" else "reset_zero",
                reachable_teacher=phase == "reset", previous_inputs=u,
                previous_state=s, current_inputs=x, successor_state=successor,
                root_value=old, recipe_value=new, replay="PASS"), values


def append_samples(seq, seq_mask, samples):
    require(seq_mask >= 1 and seq_mask & (seq_mask+1) == 0, "signature mask is not contiguous")
    result, offset = list(seq), seq_mask.bit_length()
    for row in samples:
        require(len(row) == len(result) and all(type(x) is int and x in (0,1) for x in row),
                "invalid original-AIG sample")
        for i,value in enumerate(row):
            result[i] |= value << offset
        offset += 1
    return result, (1 << offset)-1


def executable_identity(path):
    stat = Path(path).stat()
    return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)


def collect_models(p, a, graph, base, step, candidates, out, helper, deadline, identity,
                   *, helper_binding=None):
    """Extract/replay models; an optional case-SHA binding avoids per-call SHA.

    A binding is accepted only from a caller that checked full helper bytes at
    case entry and checks them again at case exit/controller validation. Its
    anchored metadata is never recaptured. Standalone callers retain full
    before/after helper SHA checks by default.
    """
    bound_identity = None
    if helper_binding is not None:
        require(isinstance(helper_binding, dict) and set(helper_binding) == {"sha256", "identity"},
                "invalid case-bound helper identity")
        digest = helper_binding["sha256"]
        require(isinstance(digest, str) and len(digest) == 64 and
                all(c in "0123456789abcdef" for c in digest), "invalid bound helper SHA")
        bound_identity = tuple(helper_binding["identity"])
        require(len(bound_identity) == 5 and all(type(x) is int for x in bound_identity),
                "invalid bound executable metadata")
        guard_strategy = "case_entry_exit_and_controller_sha256; per_invocation_anchored_stat_identity"
    else:
        digest = None
        guard_strategy = "standalone_full_sha256_before_and_after_each_invocation"

    def check_bound_helper():
        if bound_identity is not None:
            require(executable_identity(helper) == bound_identity, "model executable identity changed")

    check_bound_helper()
    out.mkdir()
    roles, variables = projected_pis(graph,base,step,a)
    miters = []
    for c in candidates:
        deadline.remaining()
        expression = p.graph_recipe(graph,step,c["recipe"],c["out"])
        miters.append(graph.xor(step[c["root"]],expression))
    cnf,qfile,vfile = out/"models.cnf",out/"models.queries",out/"models.variables"
    graph.cnf(cnf)
    qfile.write_text(str(len(miters))+"\n"+"".join(f"{i} 1 {m}\n" for i,m in enumerate(miters)))
    vfile.write_text(str(len(variables))+"\n"+" ".join(map(str,variables))+"\n")
    sources = [dict(query=i, phase="image", root=c["root"], recipe=c["recipe"],out=c["out"],miter=m)
               for i,(c,m) in enumerate(zip(candidates,miters))]
    fingerprint = dict(**identity,cnf_sha256=sha(cnf),queries_sha256=sha(qfile),
                       variables_sha256=sha(vfile), helper_sha256=digest if bound_identity is not None else sha(helper),
                       helper_guard_strategy=guard_strategy, helper_stat_identity=bound_identity, roles=roles,
                       query_sources=sources)
    write_json(out/"provenance.json",fingerprint)
    start = time.monotonic()
    with (out/"helper.log").open("w") as log:
        check_bound_helper()
        try:
            proc = subprocess.run([str(helper),str(cnf),str(qfile),str(vfile),str(out/"results.csv"),str(out/"models.jsonl")],
                                  stdout=log,stderr=subprocess.STDOUT,timeout=deadline.remaining())
        finally:
            check_bound_helper()
    require(proc.returncode == 0,"model helper failed")
    require((bound_identity is not None or sha(helper)==fingerprint["helper_sha256"]) and sha(cnf)==fingerprint["cnf_sha256"] and
            sha(qfile)==fingerprint["queries_sha256"] and sha(vfile)==fingerprint["variables_sha256"],
            "model source identity changed")
    rows=list(csv.DictReader((out/"results.csv").open()))
    require([int(r["query"]) for r in rows]==list(range(len(candidates))),"incomplete model result rows")
    answers=[int(r["result"]) for r in rows]
    require(all(r in (-1,0,1) for r in answers),"invalid helper status")
    raw=[json.loads(line) for line in (out/"models.jsonl").read_text().splitlines()]
    require([r["query"] for r in raw]==[i for i,r in enumerate(answers) if r==1],"missing/extra/reordered SAT models")
    witnesses,samples,seen=[],[],{}
    for model in raw:
        deadline.remaining()
        i=model["query"]
        row,values=replay_model(a,graph,roles,variables,model["values"],candidates[i],miters[i],"image",p.recipe_eval)
        row.update(query=i,candidate_id=list(candidate_id(candidates[i])),
                   source_provenance_sha256=sha(out/"provenance.json"))
        key=tuple(row["current_inputs"]+row["successor_state"])
        if key not in seen:
            seen[key]=len(samples)
            samples.append(values)
        row["sample_index"]=seen[key]
        witnesses.append(row)
    write_json(out/"replayed_models.json",witnesses)
    report=dict(queries=len(candidates),statuses=dict(Counter(answers)),models=len(raw),
                unique_domain_samples=len(samples),duplicate_domain_samples=len(raw)-len(samples),
                unknown_skipped=answers.count(0),wall_s=time.monotonic()-start,
                conflicts=sum(int(r["conflicts"]) for r in rows),
                results_sha256=sha(out/"results.csv"),models_sha256=sha(out/"models.jsonl"),
                replayed_models_sha256=sha(out/"replayed_models.json"))
    require(-1 not in answers,"saved image-SAT source contradicted by helper")
    write_json(out/"report.json",report)
    return samples,report


def random_image_samples(a,count,seed,deadline):
    rng=random.Random(seed);samples=[];seen=set();records=[]
    while len(samples)<count:
        deadline.remaining()
        u=[rng.randrange(2) for _ in range(a.ni)]
        s=[rng.randrange(2) for _ in range(a.nl)]
        x=[rng.randrange(2) for _ in range(a.ni)]
        nxt=a.step(u,s)[1]; key=tuple(x+nxt)
        if key in seen: continue
        seen.add(key);samples.append(a.step(x,nxt)[2])
        records.append(dict(domain="unrestricted_one_step_image",reachable_teacher=False,
                            previous_inputs=u,previous_state=s,current_inputs=x,successor_state=nxt))
    return samples,records


def projection_counts(roots,seq,mask,samples):
    result=[]
    for row in roots:
        nodes=[row["root"]]+row["pool"]
        baseline={tuple((seq[node]>>lane)&1 for node in nodes) for lane in range(mask.bit_length())}
        added={tuple(values[node] for node in nodes) for values in samples}
        result.append(dict(root=row["root"],ordered_projection_nodes=nodes,
                           baseline_unique=len(baseline),learned_unique=len(added),
                           learned_new_unique=len(added-baseline),
                           duplicate_learned_projection_rows=len(samples)-len(added)))
    return result


def search_same_pool(p,s,roots,seq,seq_mask,free,free_mask,config,deadline,out):
    found,stats=[],Counter()
    with out.open("w") as log:
        for row in roots:
            deadline.remaining()
            info={int(k):v for k,v in row["pool_info"].items()}
            cs,rs=p.search_root(s,row["root"],row["pool"],info,seq,seq_mask,free,free_mask,config,deadline)
            found.extend(cs); stats.update(rs)
            log.write(json.dumps(dict(root=row["root"],search=dict(rs),candidates=len(cs)))+"\n")
    return found,dict(stats)


def prove_new(p,a,graph,base,step,reset,free,candidates,out,solver,deadline):
    out.mkdir()
    queries=[]
    for c in candidates:
        c["free_witness"]=p.witness(a,c,free)
        for mapping in (base,reset,step):
            new=p.graph_recipe(graph,mapping,c["recipe"],c["out"])
            queries.append([graph.xor(mapping[c["root"]],new)])
    answers,report=p.run_queries(graph,queries,out,solver,deadline)
    for i,c in enumerate(candidates):
        status=answers[3*i:3*i+3]
        require(status[0]!=-1,"free proof contradicts original-AIG witness")
        c["diagnostic_proof"]={k:{-1:"UNSAT",0:"UNKNOWN",1:"SAT"}[v] for k,v in zip(("free","reset","image"),status)}
        c["qualified_offline_opportunity"]=status==[1,-1,-1]
    write_json(out/"candidates.json",candidates)
    write_json(out/"report.json",report)
    return report


def run_case(p,run,name,out,helper,solver,seconds):
    out.mkdir()
    deadline=p.Deadline(seconds)
    source=run/name
    job=json.loads((source/"job.json").read_text())
    cfg=p.Config(**job["config"])
    require(job["chunk_roots"]==32,"fixed first32 protocol requires chunk_roots=32")
    roots=[json.loads(x) for x in (source/"root_search.jsonl").read_text().splitlines()][:32]
    old=json.loads((source/"chunks/chunk_00000/candidates.json").read_text())
    case=job["case"]; path=Path(case["input"])
    require(sha(path)==case["input_sha256"],"input hash mismatch")
    identity=dict(input_sha256=sha(path),source_candidates_sha256=sha(source/"chunks/chunk_00000/candidates.json"),
                  source_roots_sha256=sha(source/"root_search.jsonl"),source_runtime_sha256=sha(p.__file__),
                  config=job["config"],chunk="chunk_00000")
    write_json(out/"provenance.json",identity)
    a=p.Aiger(path); s=p.Structure(a); graph,base,step,reset=p.compile_graph(a)
    bound=verify_source(p,run,source,job,old,graph,dict(free=base,reset=reset,step=step),out,solver)
    bound.update({helper:sha(helper),path:identity["input_sha256"],
                  source/"chunks/chunk_00000/candidates.json":identity["source_candidates_sha256"],
                  source/"root_search.jsonl":identity["source_roots_sha256"]})
    (free,image,initial),mask=p.signatures(graph,[base,step,reset],cfg)
    seq=[i|(r<<cfg.lanes) for i,r in zip(image,initial)];seq_mask=(1<<(2*cfg.lanes))-1
    start=time.monotonic()
    control,control_stats=search_same_pool(p,s,roots,seq,seq_mask,free,mask,cfg,deadline,out/"control_roots.jsonl")
    control_wall=time.monotonic()-start
    require([candidate_id(c) for c in control]==[candidate_id(c) for c in old],"frozen control candidate mismatch")
    recorded=Counter()
    for row in roots: recorded.update(row["search"])
    require(control_stats==dict(recorded),"frozen control discovery metrics mismatch")
    failed=[c for c in old if c["proof"]["step"]=="SAT"]
    samples,model_report=collect_models(p,a,graph,base,step,failed,out/"models",helper,deadline,identity)
    write_json(out/"targeted_projection_counts.json",projection_counts(roots,seq,seq_mask,samples))
    refined,refined_mask=append_samples(seq,seq_mask,samples)
    start=time.monotonic()
    updated,updated_stats=search_same_pool(p,s,roots,refined,refined_mask,free,mask,cfg,deadline,out/"refined_roots.jsonl")
    updated_wall=time.monotonic()-start
    start=time.monotonic()
    random_samples,random_records=random_image_samples(a,len(samples),2026100207,deadline)
    random_generation_wall=time.monotonic()-start
    write_json(out/"random_models.json",random_records)
    write_json(out/"random_projection_counts.json",projection_counts(roots,seq,seq_mask,random_samples))
    random_seq,random_mask=append_samples(seq,seq_mask,random_samples)
    start=time.monotonic()
    random_found,random_stats=search_same_pool(p,s,roots,random_seq,random_mask,free,mask,cfg,deadline,out/"random_roots.jsonl")
    random_wall=time.monotonic()-start
    old_ids={candidate_id(c) for c in old}; updated_ids={candidate_id(c) for c in updated}
    random_ids={candidate_id(c) for c in random_found}
    known_good=[c for c in old if c["qualified_offline_opportunity"]]
    # Appended image samples must never contradict a baseline image-valid proof.
    for c in known_good:
        require(p.recipe_eval(c["recipe"],c["out"],refined,refined_mask)==refined[c["root"]],
                "hard image sample contradicts baseline proof class")
    new_map={candidate_id(c):c for c in updated+random_found if candidate_id(c) not in old_ids}
    new=list(new_map.values())
    proof_report=prove_new(p,a,graph,base,step,reset,free,new,out/"new_proofs",solver,deadline)
    result=dict(case=name,status="COMPLETE",root_count=len(roots),control_reproduced=True,
                control=dict(candidates=len(old),stats=control_stats,search_wall_s=control_wall),
                models=model_report,refined=dict(candidates=len(updated),stats=updated_stats,search_wall_s=updated_wall),
                random=dict(candidates=len(random_found),stats=random_stats,search_wall_s=random_wall,
                            generation_wall_s=random_generation_wall,samples=len(random_samples),seed=2026100207),
                old_candidates_refuted=sum(p.recipe_eval(c["recipe"],c["out"],refined,refined_mask)!=refined[c["root"]] for c in old),
                retained_old_candidates=len(old_ids&updated_ids),new_candidates=len(updated_ids-old_ids),
                new_qualified=sum(c["qualified_offline_opportunity"] for c in new if candidate_id(c) in updated_ids),
                random_new_candidates=len(random_ids-old_ids),
                random_new_qualified=sum(c["qualified_offline_opportunity"] for c in new if candidate_id(c) in random_ids),
                known_proved_candidates=len(known_good),known_proved_sample_consistent=True,
                known_proved_retained_in_topk=sum(candidate_id(c) in updated_ids for c in known_good),
                proof_report=proof_report,elapsed_s=time.monotonic()-deadline.start,
                area_measured=False,same_budget_claim=False,
                native_novelty="NOT_CHECKED",domain="reset_union_unrestricted_image")
    write_json(out/"refined_candidates.json",updated)
    write_json(out/"random_candidates.json",random_found)
    for path,expected in bound.items(): require(sha(path)==expected,"source/executable changed during diagnostic")
    write_json(out/"verified_source_hashes.json",{str(path):value for path,value in bound.items()})
    deadline.remaining()
    write_json(out/"result.json",result)
    return result


def main():
    ap=argparse.ArgumentParser();ap.add_argument("--run",type=Path,required=True);ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--model-solver",type=Path,required=True);ap.add_argument("--solver",type=Path,required=True)
    args=ap.parse_args();require(not args.out.exists(),"new output directory required")
    args.out.mkdir(parents=True);protocol=json.loads((HERE/"protocol.json").read_text())
    p=load_runtime(args.run/"source")
    write_json(args.out/"plan.json",dict(protocol=protocol,protocol_sha256=sha(HERE/"protocol.json"),
        diagnostic_sha256=sha(__file__),model_source_sha256=sha(HERE/"model_solver.c"),
        runtime=str(Path(p.__file__).resolve()),run=str(args.run.resolve()),
        helper_sha256=sha(args.model_solver),solver_sha256=sha(args.solver)))
    rows=[]
    for name in protocol["cases"]:
        start=time.monotonic()
        try: result=run_case(p,args.run,name,args.out/name,args.model_solver.resolve(),args.solver.resolve(),protocol["budget_seconds_per_case"])
        except Exception as error:
            result=dict(case=name,status="TIMEOUT" if isinstance(error,(TimeoutError,subprocess.TimeoutExpired)) else "ERROR",error=repr(error),elapsed_s=time.monotonic()-start)
            write_json(args.out/name/"result.json",result)
        rows.append(result);write_json(args.out/"results.json",rows)
        print(json.dumps(result),flush=True)


if __name__=="__main__": main()
