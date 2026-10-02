#!/usr/bin/env python3
"""Ordered complete-case annotation/admission/proof/checkpoint semantic worklist.

Preparation stores paths/hashes and operation order, never copies raw proof data.
Replay performs no search or solver call and reports no performance comparison.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as stream:
        for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def read(path):return json.loads(Path(path).read_text())
def write(path,value):Path(path).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def identity(c):return c['root'],tuple(c['recipe']),c['out']
def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def prepare(case,out):
    assert not out.exists();case=case.resolve();result=read(case/'result.json');job=read(case/'job.json')
    assert result['status']=='COMPLETE','ordered gate uses fixed COMPLETE cases only'
    roots=[json.loads(line)for line in (case/'root_search.jsonl').read_text().splitlines()]
    notices={}
    for notice in result['driver']['observed_checkpoints']:
        metadata=read(case/'checkpoints'/notice['directory']/'checkpoint.json')
        index=metadata['progress'].get('proof_completed_chunks',0)
        assert index not in notices;notices[index]=notice
    ops=[dict(op='CHECKPOINT',notice=notices[0]),dict(op='INIT')];chunk_index=round_index=0;model_attempted=set()
    for offset in range(0,len(roots),job['chunk_roots']):
        group=roots[offset:offset+job['chunk_roots']];chunk=case/'chunks'/f'chunk_{chunk_index:05d}'
        cs=read(chunk/'candidates.unproved.json');counts=Counter(c['root']for c in cs)
        assert counts==Counter({r['root']:r['candidates']for r in group if r['candidates']})
        for row in group:
            ops.append(dict(op='ANNOTATE',kind='initial',root=row['root'],chunk=chunk.name,
                            indexes=[i for i,c in enumerate(cs)if c['root']==row['root']]))
        while True:
            chunk=case/'chunks'/f'chunk_{chunk_index:05d}';cs=read(chunk/'candidates.json')
            ops.append(dict(op='PROOF',chunk=chunk.name))
            if chunk_index+1 in notices:ops.append(dict(op='CHECKPOINT',notice=notices[chunk_index+1]))
            source_indexes=[i for i,c in enumerate(cs)if c['proof']['reset']=='UNSAT'and c['proof']['free']=='SAT'and
                            c['proof']['step']=='SAT'and identity(c)not in model_attempted]
            model_attempted.update(identity(cs[i])for i in source_indexes)
            if not source_indexes:break
            round_name=f'round_{round_index:05d}';refinement=read(case/'image_guidance'/round_name/'refinement.json')
            ops.append(dict(op='ADMIT',chunk=chunk.name,indexes=source_indexes,round=round_name))
            new_count=refinement['new_candidates']
            if refinement['discovery_executed_roots']+refinement['discovery_skipped_unchanged_projection_roots']:
                next_chunk=f'chunk_{chunk_index+1:05d}' if new_count else None
                if new_count:assert len(read(case/'chunks'/next_chunk/'candidates.unproved.json'))==new_count
                ops.append(dict(op='ANNOTATE',kind='refinement',round=round_name,chunk=next_chunk,indexes=list(range(new_count))))
            round_index+=1
            if not new_count:break
            chunk_index+=1
        chunk_index+=1
    assert chunk_index==len(list((case/'chunks').glob('chunk_*/candidates.unproved.json')))
    assert round_index==len(list((case/'image_guidance').glob('round_*/refinement.json')))
    ops.append(dict(op='FINAL'))
    bound={str(path):sha(path)for path in sorted(case.rglob('*'))if path.is_file()}
    bound[str(case.parent/'plan.json')]=sha(case.parent/'plan.json')
    for name,h in job['source_hashes'].items():
        path=case.parent/'source'/name;assert sha(path)==h;bound[str(path)]=h
    bound[job['case']['input']]=job['case']['input_sha256']
    write(out,dict(schema=1,status='PREPARED_SEMANTIC_WORKLIST',case=str(case),operations=ops,source_artifacts=bound,
                   source_job_sha256=sha(case/'job.json'),original_proof_source_hashes=job['source_hashes'],
                   roots=len(roots),proof_chunks=chunk_index,refinements=round_index,performance_comparison='NOT_RUN'))

def replay(plan_path,source,out,use_cache):
    assert not out.exists();out.mkdir(parents=True);plan=read(plan_path);case=Path(plan['case']);source=source.resolve()
    assert plan['status']=='PREPARED_SEMANTIC_WORKLIST'
    for path,h in plan['source_artifacts'].items():assert sha(path)==h
    sys.path.insert(0,str(source/'nonlinear_divisors'))
    import prototype as p
    import free_guided as fg
    import anytime as at
    import inline_models as im
    import product
    assert Path(fg.__file__).resolve()==source/'nonlinear_divisors/free_guided.py'
    job=read(case/'job.json');variant={name:sha(source/name)for name in job['source_hashes']}
    if use_cache:variant['nonlinear_divisors/free_manifest_cache.py']=sha(source/'nonlinear_divisors/free_manifest_cache.py')
    # Output routing is an explicit adapter, not a rewritten saved proof/job.
    work=out/'replay';work.mkdir()
    for name in ('chunks','checkpoints','job.json'):(work/name).symlink_to(case/name,target_is_directory=name!='job.json')
    replay_job=dict(job,out=str(work),free_manifest_cache=use_cache)
    a=p.Aiger(job['case']['input']);g,base,step,reset=p.compile_graph(a);maps=dict(free=base,reset=reset,step=step)
    cfg=p.Config(**job['config']);(initial_free,_,_),mask=p.signatures(g,[base,step,reset],cfg)
    clock=p.Deadline(120);helper=cache=None;events=[];candidates={}
    def cs(chunk,proved=False):
        key=(chunk,proved)
        if key not in candidates:candidates[key]=read(case/'chunks'/chunk/('candidates.json'if proved else 'candidates.unproved.json'))
        return candidates[key]
    def compare_domains():
        for path in sorted((work/'free_domains').glob('version_*.json')):
            assert sha(path)==sha(case/'free_domains'/path.name)
    try:
        for op in plan['operations']:
            clock.remaining();kind=op['op']
            if kind=='INIT':
                helper=fg.PredecessorFreeDomain(a,g,base,step,initial_free,mask,replay_job,cfg,clock)
                cache=getattr(helper,'manifest_cache',None);assert bool(cache)==use_cache;compare_domains()
                events.append(dict(op=kind,domain_hash=helper.state.snapshot().domain_sha256))
            elif kind=='ANNOTATE':
                original=[cs(op['chunk'])[i]for i in op['indexes']]if op['chunk']else []
                copied=json.loads(json.dumps(original))
                for candidate in copied:candidate.pop('free_domain',None)
                helper.annotate(copied)
                # Fresh dataclass annotations may contain tuples; the saved
                # JSON has arrays. Require exact canonical serialization.
                assert digest(copied)==digest(original)
                events.append(dict(op=kind,kind=op['kind'],version=helper.state.snapshot().version,
                                   candidates=len(copied),candidate_digest=digest(copied)))
            elif kind=='PROOF':
                rows=cs(op['chunk']);snapshot=helper.state.snapshot();verified=[]
                def verify():
                    for c in rows:
                        clock.remaining();assert p.witness(a,c,snapshot.signatures)==c['free_witness']
                        value=(fg.verify_witness_annotation(a,c,c['free_witness'],work,job['case']['input_sha256'],cache)
                               if cache else fg.verify_witness_annotation(a,c,c['free_witness'],work,job['case']['input_sha256']))
                        verified.append(value)
                    graph=p.Graph();graph.gates=list(g.gates);graph.hash=dict(g.hash);literals=[]
                    for c in rows:
                        clock.remaining();row={}
                        for phase,mapping in maps.items():
                            value=p.graph_recipe(graph,mapping,c['recipe'],c['out']);row[phase]=graph.xor(mapping[c['root']],value)
                        literals.append(row)
                    assert literals==read(case/'chunks'/op['chunk']/'query_literals.json')
                    assert im.graph_cnf_sha256(graph)==sha(case/'chunks'/op['chunk']/'obligations.cnf')
                if cache:
                    with cache.proof_boundary(rows):verify()
                else:verify()
                events.append(dict(op=kind,chunk=op['chunk'],witness_digest=digest(verified),count=len(rows)))
            elif kind=='ADMIT':
                target=case/'image_guidance'/op['round'];refinement=read(target/'refinement.json')
                sources=[cs(op['chunk'],True)[i]for i in op['indexes']]
                actual=helper.admit(sources,target,refinement['model_report'],read(target/'replayed_models.json'))
                assert digest(actual)==digest(read(target/'free_admission.json'));compare_domains()
                events.append(dict(op=kind,round=op['round'],admission_digest=digest(actual),
                    unchanged_saved_sequence_signature=refinement['construction_signature_sha256']))
            elif kind=='CHECKPOINT':
                notice=op['notice'];path,metadata=at.verify_checkpoint(work,notice,job['case']['input_sha256'],free_domain_required=True)
                selected=read(path/'selection.json')['selected']
                rebuilt=product.rebuild(a,selected);product.write_aig(out/'product-replay.aig',rebuilt)
                assert sha(out/'product-replay.aig')==sha(path/'product.aig')
                if cache:cache.authenticate([c['free_domain']['manifest']for c in selected])
                events.append(dict(op=kind,checkpoint=path.name,product_sha256=sha(path/'product.aig')))
            elif kind=='FINAL':
                if cache:cache.verify_all()
                compare_domains();assert len(helper.manifests)==len(list((case/'free_domains').glob('version_*.json')))
                events.append(dict(op=kind,versions=len(helper.manifests),domain_hash=helper.state.snapshot().domain_sha256))
            else:raise AssertionError(kind)
        if cache:cache.close()
        for path,h in plan['source_artifacts'].items():assert sha(path)==h
        for name,h in variant.items():assert sha(source/name)==h
        write(out/'result.json',dict(status='PASS_ORDERED_SAVED_SEMANTICS',events=events,events_sha256=digest(events),
              worklist=str(plan_path),worklist_sha256=sha(plan_path),original_job_sha256=plan['source_job_sha256'],
              original_proof_source_hashes=job['source_hashes'],variant_source_hashes=variant,
              adapter_output_directory=str(work),original_provenance_rewritten=False,cache_report=cache.report()if cache else None,
              no_search=True,no_solver=True,no_DSEC=True,no_transform=True,performance_comparison='NOT_RUN',checker_sha256=sha(__file__)))
        print(json.dumps(dict(status='PASS_ORDERED_SAVED_SEMANTICS',events=len(events),events_sha256=digest(events))),flush=True)
    finally:
        if cache:cache.close()

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--prepare-case',type=Path)
    parser.add_argument('--worklist',type=Path);parser.add_argument('--source',type=Path);parser.add_argument('--cache',action='store_true')
    parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
    if args.prepare_case:prepare(args.prepare_case,args.out)
    else:replay(args.worklist,args.source,args.out,args.cache)
