#!/usr/bin/env python3
"""Read-only semantic replay of completed frozen v1 guidance prefixes.

Re-enumerates the saved initial pools/signature versions, compares complete
candidate dictionaries with projection-skipped results, rebuilds ordinary proof
CNFs, and replays query scheduling with frozen responses. Runs NO proof/model
solver, creates NO new product, and makes NO area or timing claim.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
import copy
import csv
import json
from pathlib import Path
import time
from unittest.mock import patch

import anytime as at
import image_guided as ig
p=ig.p


def read(path):
    return json.loads(Path(path).read_text())


def rows(path):
    return [json.loads(x) for x in Path(path).read_text().splitlines()]


def semantic(candidate):
    return {k:v for k,v in candidate.items() if k not in
            {"free_witness","proof","qualified_offline_opportunity","anytime_certificate","image_guidance"}}


def check_proof_inputs(graph, mappings, candidates, source, out, job, deadline):
    rebuilt=p.Graph();rebuilt.gates=list(graph.gates);rebuilt.hash=dict(graph.hash)
    literals=[]
    for c in candidates:
        literal={}
        for phase,mapping in mappings.items():
            expression=p.graph_recipe(rebuilt,mapping,c["recipe"],c["out"])
            literal[phase]=rebuilt.xor(mapping[c["root"]],expression)
        literals.append(literal)
    out.mkdir()
    broker=at.FrozenQueries(rebuilt,out,Path(job["solver"]),deadline,job["solver_identity"])
    p.require(broker.fingerprint==p.sha(source/"obligations.cnf"),"replayed proof CNF differs")
    p.require(literals==read(source/"query_literals.json"),"replayed proof literals differ")
    batches=read(source/"proof_report.json")["batches"];called=[]
    def saved_batch(queries,phase):
        expected=batches[len(called)];p.require(expected["phase"]==phase,"proof phase order differs")
        qlines=(source/expected["queries_file"]).read_text().splitlines()
        expected_queries=[]
        for i,line in enumerate(qlines[1:]):
            values=list(map(int,line.split()));p.require(values[:2]==[i,len(values)-2],"bad frozen query")
            expected_queries.append(values[2:])
        p.require(int(qlines[0])==len(queries) and expected_queries==[list(q) for q in queries],"proof assumptions/order differ")
        with (source/expected["results_file"]).open() as stream: answers=[int(r["result"]) for r in csv.DictReader(stream)]
        called.append(expected["queries_sha256"])
        return answers,[dict(result=at.STATUS[a],reused=False) for a in answers]
    statuses=[dict(free="NOT_RUN",reset="NOT_RUN",step="NOT_RUN") for _ in candidates]
    with patch.object(broker,"_batch",side_effect=saved_batch):
        indexes=list(range(len(candidates)))
        for phase in ("reset","free","step"):
            answers,_=broker.solve([[literals[i][phase]] for i in indexes],phase)
            for i,a in zip(indexes,answers):statuses[i][phase]=at.STATUS[a]
            indexes=[i for i,a in zip(indexes,answers) if a==(1 if phase=="free" else -1)]
    p.require(len(called)==len(batches),"unreplayed proof batch")
    for c,s in zip(candidates,statuses):p.require(all(c["proof"][k]==v for k,v in s.items()),"frozen status scheduling differs")
    (out/"obligations.cnf").unlink() # Keep exact hashes, not duplicate large proof files.
    result=dict(candidates=len(candidates),cnf_sha256=broker.fingerprint,query_file_sha256=called,status="PASS")
    p.write_json(out/"comparison.json",result)
    return result


def run_case(run,name,out):
    source=run/name;job=read(source/"job.json");config=p.Config(**job["config"])
    plan=read(run/"plan.json")
    p.require(p.sha(p.__file__)==plan["runtime_source_hashes"]["nonlinear_divisors/prototype.py"],"search implementation differs")
    p.require(p.sha(job["case"]["input"])==job["case"]["input_sha256"],"input changed")
    a=p.Aiger(job["case"]["input"]);structure=p.Structure(a);graph,base,step,reset=p.compile_graph(a)
    (free,image,initial),free_mask=p.signatures(graph,[base,step,reset],config)
    mask=(1 << (2*config.lanes))-1;seq=[x|(y << config.lanes) for x,y in zip(image,initial)]
    start=time.monotonic();deadline=at.Budget(start,start+7200)
    guide=ig.ImageGuidance(a,graph,base,step,seq,mask,free,free_mask,structure,config,job,deadline,job["image_model_solver_identity"])
    initial_rows=rows(source/"root_search.jsonl");by_version=defaultdict(list);by_root={}
    for r in initial_rows:
        r["pool_info"]={int(k):v for k,v in r["pool_info"].items()}
        by_version[r["teacher_version"]].append(r);by_root[r["root"]]=r
    actual={};processed=set();counts=defaultdict(int);round_reports=[]
    def initial_searches():
        for r in by_version[guide.version]:
            if r["root"] in processed:continue
            cs,stats=p.search_root(structure,r["root"],r["pool"],r["pool_info"],guide.seq,guide.mask,free,free_mask,config,deadline)
            p.require(dict(stats)==r["search"] and len(cs)==r["candidates"],"initial frozen search differs")
            guide.remember_search(r["root"],r["pool"],r["pool_info"],cs,stats)
            actual[r["root"],guide.version]=copy.deepcopy(cs);guide.mark_attempted(cs)
            processed.add(r["root"]);counts["initial_searches"]+=1
    for file in sorted(source.glob("image_guidance/round_*/refinement.json")):
        initial_searches();record=read(file)
        p.require(record["teacher_version_before"]==guide.version,"teacher version gap")
        search_rows=rows(file.parent/"root_search.jsonl") if (file.parent/"root_search.jsonl").exists() else []
        roots=[dict(root=r["root"],pool=r["pool"],pool_info=by_root[r["root"]]["pool_info"]) for r in search_rows]
        model_rows={r["sample_index"]:r for r in read(file.parent/"replayed_models.json")}
        samples=[a.step(model_rows[i]["current_inputs"],model_rows[i]["successor_state"])[2] for i in range(len(model_rows))]
        keys=[model_rows[i]["current_inputs"]+model_rows[i]["successor_state"] for i in range(len(model_rows))]
        added,decisions=ig.select_new_samples(roots,guide.seq,guide.mask,samples,keys,guide.seen_keys)
        p.require(decisions==record["decisions"] and len(added)==record["accepted_samples"],"model admission decisions differ")
        guide.seq,guide.mask=ig.d.append_samples(guide.seq,guide.mask,added)
        guide.version+=int(bool(added));p.require(guide.version==record["teacher_version_after"],"teacher version changed")
        changed={root for d in decisions if d["decision"]=="APPEND_IMAGE_CONSTRAINT" for root in d["relevant_roots"]}
        fresh_all=[];skipped=0
        for row,saved in zip(roots,search_rows):
            original,stats=p.search_root(structure,row["root"],row["pool"],row["pool_info"],guide.seq,guide.mask,free,free_mask,config,deadline)
            optimized,optimized_stats=guide.search_again(row,row["root"] in changed)
            p.require(original==optimized and stats==optimized_stats,"full candidate recipe/cost/witness differential failed")
            p.require(dict(stats)==saved["search"] and len(original)==saved["candidates"],"replayed frozen search differs")
            fresh=[c for c in optimized if ig.d.candidate_id(c) not in guide.attempted]
            p.require(len(fresh)==saved["untried_candidates"],"untried candidate count differs")
            actual[row["root"],guide.version]=copy.deepcopy(fresh);fresh_all.extend(fresh)
            skipped+=int(row["root"] not in changed);counts["refinement_root_comparisons"]+=1
            counts["complete_topk_candidate_comparisons"]+=len(original)
        guide.mark_attempted(fresh_all)
        p.require(len(fresh_all)==record["new_candidates"],"refined proof candidate count differs")
        counts["skipped_roots"]+=skipped;counts["accepted_global_samples"]+=len(added)
        round_reports.append(dict(round=file.parent.name,status="PASS",roots=len(roots),skipped_roots=skipped,new_candidates=len(fresh_all)))
    initial_searches()
    proof_reports=[]
    (out/"proof_inputs").mkdir(parents=True)
    for file in sorted(source.glob("chunks/chunk_*/proof_report.json")):
        candidates=read(file.parent/"candidates.json");groups=[]
        for c in candidates:
            key=c["root"],c["image_guidance"]["teacher_version"]
            if not groups or groups[-1]!=key:groups.append(key)
        reconstructed=[c for key in groups for c in actual[key]]
        p.require(reconstructed==[semantic(c) for c in candidates],"complete proof candidate list identity/order/cost differs")
        proof_reports.append(check_proof_inputs(graph,dict(free=base,reset=reset,step=step),candidates,file.parent,out/"proof_inputs"/file.parent.name,job,deadline))
    counts["proof_chunks"]=len(proof_reports);counts["proof_candidates"]=sum(r["candidates"] for r in proof_reports)
    result=dict(case=name,status="PASS",counts=dict(counts),rounds=round_reports,proof_inputs=proof_reports,
        solver_invocations=0,scope="completed frozen discovery/proof-input prefixes only; no new gain/timing measurement")
    p.write_json(out/"report.json",result);print(json.dumps(dict(case=name,status="PASS",counts=dict(counts))),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--run",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True);parser.add_argument("--cases",nargs="+")
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=False)
    names=args.cases or [Path(x).stem for x in read(args.run/"plan.json")["cases"]]
    results=[run_case(args.run,name,args.out/name) for name in names]
    p.write_json(args.out/"report.json",dict(status="PASS",source_run=str(args.run),cases=results,
        reviewed_source_sha256={name:p.sha(Path(__file__).parent/name) for name in ["anytime.py","image_guided.py","audit_projection_skip.py"]}))


if __name__=="__main__":main()
