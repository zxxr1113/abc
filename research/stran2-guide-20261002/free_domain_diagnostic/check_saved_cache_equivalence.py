#!/usr/bin/env python3
"""Fixed saved-record semantic replay; no search, solver, timing or provenance edit."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--case',type=Path,required=True)
    ap.add_argument('--source',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--cache',action='store_true');args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=False)
    bound={}
    def read(path):
        path=Path(path);data=path.read_bytes();bound[str(path)]=hashlib.sha256(data).hexdigest();return json.loads(data)
    case=args.case.resolve();source=args.source.resolve();job=read(case/'job.json');plan=read(case.parent/'plan.json')
    assert job['source_hashes']==plan['runtime_source_hashes']
    for name,h in job['source_hashes'].items():
        path=case.parent/'source'/name;assert sha(path)==h;bound[str(path)]=h
    # Variant code is bound separately; it never replaces the old job's source
    # map, proof receipt, raw model manifest or candidate provenance fields.
    variant={name:sha(source/name)for name in job['source_hashes']}
    if args.cache:variant['nonlinear_divisors/free_manifest_cache.py']=sha(source/'nonlinear_divisors/free_manifest_cache.py')
    sys.path.insert(0,str(source/'nonlinear_divisors'))
    import prototype as p
    import free_guided as fg
    import anytime as at
    import inline_models as im
    import product
    assert Path(p.__file__).resolve()==source/'nonlinear_divisors/prototype.py'
    assert Path(fg.__file__).resolve()==source/'nonlinear_divisors/free_guided.py'
    clock=p.Deadline(120);input_path=Path(job['case']['input']);assert sha(input_path)==job['case']['input_sha256']
    bound[str(input_path)]=job['case']['input_sha256'];a=p.Aiger(input_path)
    graph,base,step,reset=p.compile_graph(a);maps=dict(free=base,reset=reset,step=step)
    (initial_free,_,_),_=p.signatures(graph,[base,step,reset],p.Config(**job['config']))
    cache=None
    if args.cache:
        from free_manifest_cache import ManifestCache
        cache=ManifestCache(case,job['case']['input_sha256'],(a.ni,a.nl),clock)
    semantic=dict(domains=[],chunks=[],checkpoints=[])
    try:
        for path in sorted((case/'free_domains').glob('version_*.json')):
            clock.remaining();payload=read(path)
            reference=dict(file=path.name,sha256=sha(path),free_version=payload['free_version'],
                           free_domain_sha256=payload['free_domain_sha256'],free_signature_bits=payload['free_signature_bits'])
            free,manifest=fg.reconstruct_free_manifest(a,case,reference,job['case']['input_sha256'],initial_free)
            assert manifest==payload
            if cache:cache.register(reference,payload)
            semantic['domains'].append(dict(reference=reference,free_vector_digest=digest(free),records_digest=digest(payload['records'])))
        for path in sorted((case/'chunks').glob('chunk_*/candidates.unproved.json')):
            clock.remaining();candidates=read(path);verified=[]
            def verify():
                for candidate in candidates:
                    clock.remaining()
                    value=(fg.verify_witness_annotation(a,candidate,candidate['free_witness'],case,job['case']['input_sha256'],cache)
                           if cache else fg.verify_witness_annotation(a,candidate,candidate['free_witness'],case,job['case']['input_sha256']))
                    verified.append([candidate['root'],candidate['recipe'],candidate['out'],value,digest(candidate['free_witness'])])
            if cache:
                with cache.proof_boundary(candidates):verify()
            else:verify()
            rebuilt=p.Graph();rebuilt.gates=list(graph.gates);rebuilt.hash=dict(graph.hash);literals=[]
            for candidate in candidates:
                clock.remaining();row={}
                for phase,mapping in maps.items():
                    value=p.graph_recipe(rebuilt,mapping,candidate['recipe'],candidate['out'])
                    row[phase]=rebuilt.xor(mapping[candidate['root']],value)
                literals.append(row)
            cnf=path.parent/'obligations.cnf';literal_path=path.parent/'query_literals.json'
            status='UNPUBLISHED_TAIL_NO_CNF'
            if cnf.exists():
                assert im.graph_cnf_sha256(rebuilt)==sha(cnf);bound[str(cnf)]=sha(cnf)
                assert literals==read(literal_path);status='EXACT_ORIGINAL_CNF_AND_ASSUMPTIONS'
            semantic['chunks'].append(dict(chunk=path.parent.name,candidates_digest=digest(candidates),
                witnesses=verified,cnf_sha256=sha(cnf)if cnf.exists()else None,proof_binding=status))
        result=read(case/'result.json')
        for notice in result['driver']['observed_checkpoints']:
            clock.remaining();checkpoint,metadata=at.verify_checkpoint(case,notice,job['case']['input_sha256'],free_domain_required=True)
            selection=read(checkpoint/'selection.json');selected=selection['selected']
            if cache:cache.authenticate([c['free_domain']['manifest']for c in selected])
            rebuilt=product.rebuild(a,selected);path=args.out/'checkpoint-replay.aig';product.write_aig(path,rebuilt)
            assert sha(path)==sha(checkpoint/'product.aig')
            semantic['checkpoints'].append(dict(directory=checkpoint.name,selection_digest=digest(selection),
                product_sha256=sha(path),gain=notice['gain']))
            for name,h in metadata['artifacts'].items():
                assert sha(checkpoint/name)==h;bound[str(checkpoint/name)]=h
            bound[str(checkpoint/'checkpoint.json')]=notice['manifest_sha256']
        if cache:cache.verify_all();cache.close()
        for path,h in bound.items():assert sha(path)==h
        for name,h in variant.items():assert sha(source/name)==h
        output=dict(status='PASS_FIXED_SAVED_RECORD_SEMANTICS',semantic=semantic,semantic_sha256=digest(semantic),
            original_case=str(case),original_job_sha256=bound[str(case/'job.json')],original_proof_source_hashes=job['source_hashes'],
            variant_source=str(source),variant_source_hashes=variant,cache_report=cache.report()if cache else None,
            old_provenance_unchanged=True,source_artifacts=bound,new_solver_queries=0,new_DSEC_runs=0,
            search_runs=0,transform_runs=0,performance_comparison='NOT_RUN',checker_sha256=sha(__file__))
        (args.out/'result.json').write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
        print(json.dumps(dict(status=output['status'],semantic_sha256=output['semantic_sha256'],
            domains=len(semantic['domains']),witnesses=sum(len(c['witnesses'])for c in semantic['chunks']),checkpoints=len(semantic['checkpoints']))))
    finally:
        if cache:cache.close()

if __name__=='__main__':main()
