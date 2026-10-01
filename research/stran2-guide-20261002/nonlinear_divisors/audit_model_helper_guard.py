#!/usr/bin/env python3
"""Extra-cost exact model/proof-input differential for the v3 helper guard.

Fresh model-helper invocations must reproduce every frozen completed round's
CNF, queries, projection variables, full SAT assignments, replayed witnesses and
samples. Ordinary proof CNFs/query scheduling are reconstructed with recorded
responses, without rerunning the proof solver or publishing a new product.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path
import time
from unittest.mock import patch

import anytime as at
import image_guided as ig
from audit_projection_skip import check_proof_inputs
p,d=ig.p,ig.d


def read(path):return json.loads(Path(path).read_text())


def without_provenance(rows):
    return [{k:v for k,v in row.items() if k!='source_provenance_sha256'} for row in rows]


def run_case(run,name,out,helper):
    source=run/name;job=read(source/'job.json');plan=read(run/'plan.json')
    p.require(p.sha(p.__file__)==plan['runtime_source_hashes']['nonlinear_divisors/prototype.py'],'proof/search runtime changed')
    p.require(p.sha(job['case']['input'])==job['case']['input_sha256'],'input changed')
    identity,digest=at.bind_executable(helper,job['image_model_solver_sha256'])
    a=p.Aiger(job['case']['input']);graph,base,step,reset=p.compile_graph(a)
    start=time.monotonic();deadline=at.Budget(start,start+7200);out.mkdir(parents=True)
    reports=[];helper_hash_calls=0
    for file in sorted(source.glob('image_guidance/round_*/refinement.json')):
        previous=file.parent;provenance=read(previous/'provenance.json')
        candidates=[dict(root=x['root'],recipe=x['recipe'],out=x['out'])for x in provenance['query_sources']]
        clone=p.Graph();clone.gates=list(graph.gates);clone.hash=dict(graph.hash)
        metadata={k:v for k,v in provenance.items() if k not in
            {'cnf_sha256','queries_sha256','variables_sha256','helper_sha256','helper_guard_strategy',
             'helper_stat_identity','roles','query_sources'}}
        metadata['source_hashes']={name:p.sha(Path(__file__).parent/name) for name in
                                  ['anytime.py','image_guided.py','audit_model_helper_guard.py']}
        metadata['source_hashes']['diagnostic.py']=p.sha(d.__file__)
        metadata['audit_source_round']=str(previous);target=out/file.parent.name
        with patch.object(d,'sha',wraps=d.sha) as hashes:
            samples,report=d.collect_models(p,a,clone,base,step,candidates,target,helper,deadline,metadata,
                                           helper_binding=dict(sha256=digest,identity=identity))
        calls=sum(Path(x.args[0])==helper for x in hashes.call_args_list);helper_hash_calls+=calls
        p.require(calls==0,'bound call rehashed helper bytes')
        for filename in ['models.cnf','models.queries','models.variables','models.jsonl']:
            p.require(p.sha(previous/filename)==p.sha(target/filename),'model query/assignment bytes differ: '+filename)
        old_replay,new_replay=read(previous/'replayed_models.json'),read(target/'replayed_models.json')
        p.require(without_provenance(old_replay)==without_provenance(new_replay),'full replayed witness differs')
        unique={r['sample_index']:r for r in old_replay}
        expected=[a.step(unique[i]['current_inputs'],unique[i]['successor_state'])[2]for i in range(len(unique))]
        p.require(samples==expected,'returned full original-graph samples differ')
        with (previous/'results.csv').open() as stream:old=list(csv.DictReader(stream))
        with (target/'results.csv').open() as stream:new=list(csv.DictReader(stream))
        for key in ['query','result','conflicts']:
            p.require([r[key]for r in old]==[r[key]for r in new],'model result/status/conflict differs')
        old_report=read(previous/'report.json');serialized_report=read(target/'report.json')
        for key in ['queries','statuses','models','unique_domain_samples','duplicate_domain_samples','unknown_skipped','conflicts']:
            p.require(serialized_report[key]==old_report[key],'model report semantics differ: '+key)
        reports.append(dict(round=file.parent.name,status='PASS',model_queries=report['queries'],models=report['models'],
                            unique_samples=report['unique_domain_samples'],in_call_helper_sha_calls=calls))
    at.bind_executable(helper,digest,identity)
    (out/'proof_inputs').mkdir();proofs=[]
    for file in sorted(source.glob('chunks/chunk_*/proof_report.json')):
        proofs.append(check_proof_inputs(graph,dict(free=base,reset=reset,step=step),read(file.parent/'candidates.json'),
                      file.parent,out/'proof_inputs'/file.parent.name,job,deadline))
    result=dict(case=name,status='PASS',rounds=reports,proof_inputs=proofs,
        counts=dict(model_rounds=len(reports),model_queries=sum(r['model_queries']for r in reports),
                    replayed_models=sum(r['models']for r in reports),unique_samples=sum(r['unique_samples']for r in reports),
                    proof_chunks=len(proofs),proof_candidates=sum(r['candidates']for r in proofs),
                    in_call_helper_sha_calls=helper_hash_calls),
        helper_binding=dict(sha256=digest,identity=identity),proof_solver_invocations=0,
        scope='additional read-only model/proof-input differential; no new product or area/timing claim')
    p.write_json(out/'report.json',result);print(json.dumps(dict(case=name,status='PASS',counts=result['counts'])),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--run',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True);parser.add_argument('--model-solver',type=Path,required=True)
    parser.add_argument('--cases',nargs='+');args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=False)
    names=args.cases or [Path(x).stem for x in read(args.run/'plan.json')['cases']]
    results=[run_case(args.run,name,args.out/name,args.model_solver.resolve())for name in names]
    p.write_json(args.out/'report.json',dict(status='PASS',source_run=str(args.run),cases=results,
        current_source_sha256={name:p.sha(Path(__file__).parent/name)for name in
            ['anytime.py','image_guided.py','audit_model_helper_guard.py']},diagnostic_sha256=p.sha(d.__file__)))


if __name__=='__main__':main()
