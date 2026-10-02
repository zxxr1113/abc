#!/usr/bin/env python3
"""Frozen saved-model replay timing. No solver, model generation, or discovery."""
from pathlib import Path
from collections import Counter
from contextlib import contextmanager
import copy, hashlib, json, os, platform, resource, shutil, signal, subprocess, sys, threading, time, traceback
ROOT = Path(__file__).resolve().parent
CORRECT = Path('/workspace/shared/stran2-cone-validator-correctness-v1')
SOURCE = CORRECT / 'source'
PILOT = Path('/workspace/shared/stran2-inline-model-pilot6-prepared-v1')
PROPOSAL_SHA = '76774d2fa3f1c4cf1702d16b9f8eefbf5e29864bb5985ed5c12b8b36f431f16e'
SOURCE_SHA = 'a3a1dbf2609def7a186cf13be4591ad61baa6c3a3e09f220e813f4bf8e3e3fa2'

def read(path): return json.loads(Path(path).read_text())
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def digest(obj): return hashlib.sha256(json.dumps(obj, separators=(',', ':'), sort_keys=True).encode()).hexdigest()
def write(path, obj):
    path = Path(path); temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n'); temp.replace(path)
def require(ok, message):
    if not ok: raise ValueError(message)
def utc(): return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
def capacities():
    memory = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
    return dict(free_disk_bytes=shutil.disk_usage(ROOT).free,
                available_memory_bytes=int(memory['MemAvailable'].split()[0])*1024)
def capacity_check(plan):
    actual = capacities(); limits = plan['proposal']['resources']
    require(actual['free_disk_bytes'] >= limits['reserve_free_bytes'], 'disk reserve threshold')
    require(actual['available_memory_bytes'] >= limits['minimum_available_memory_bytes'], 'memory reserve threshold')
    return actual

def source_check():
    require(sha(CORRECT/'final_manifest.json') == SOURCE_SHA, 'correctness manifest changed')
    manifest = read(CORRECT/'final_manifest.json')
    for name, expected in manifest['source_hashes'].items():
        require(sha(SOURCE/name) == expected, 'frozen runtime source changed: '+name)
    return manifest

def prepare():
    require(not (ROOT/'plan.json').exists(), 'plan already exists; no overwrite')
    require(sha(CORRECT/'saved_record_timing_proposal.json') == PROPOSAL_SHA, 'proposal changed')
    source_check(); proposal = read(CORRECT/'saved_record_timing_proposal.json')
    require(sha(PILOT/'protocol.json') == proposal['input_protocol_sha256'], 'pilot protocol changed')
    results = read(PILOT/'results.json'); cases = {}; refs = read(CORRECT/'frozen-records/results.json')
    for name in proposal['cases']:
        row = next(r for r in results if r['file'] == name and r['arm'] == 'inline')
        directory = PILOT/row['relative_run']/Path(name).stem
        job = read(directory/'job.json'); files = {str(directory/'job.json'), str(directory/'root_search.jsonl')}
        rounds = []; chunks = set()
        for saved in sorted(directory.glob('image_guidance/round_*')):
            if not (saved/'refinement.json').exists(): continue
            reference = CORRECT/'frozen-records'/Path(name).stem/saved.name
            for path in [saved/'refinement.json', saved/'replayed_models.json', reference/'differential.json', reference/'full/replayed_models.json']:
                files.add(str(path))
            stored = read(saved/'replayed_models.json')
            require(stored, 'empty completed model round')
            chunks.update(r['source_chunk'] for r in stored)
            rounds.append(dict(name=saved.name, saved=str(saved), reference=str(reference), models=len(stored)))
        for chunk in sorted(chunks):
            files.add(str(directory/'chunks'/chunk/'candidates.json'))
        ref = next(r for r in refs if r['case'] == name)
        require(len(rounds) == ref['rounds'] and sum(r['models'] for r in rounds) == ref['models'], 'reference coverage mismatch')
        cases[name] = dict(directory=str(directory), rounds=rounds, expected=ref,
                           selection_reference_hashes={path:sha(path) for path in sorted(files)})
    plan = dict(schema=1, status='FROZEN_BEFORE_TRIALS', prepared_utc=utc(), proposal=proposal,
                proposal_sha256=PROPOSAL_SHA, source_manifest_sha256=SOURCE_SHA, harness_sha256=sha(__file__),
                cases=cases, platform=dict(uname=list(platform.uname()), python=sys.version, executable=sys.executable,
                cpu_count=os.cpu_count()), reference_results_sha256=sha(CORRECT/'frozen-records/results.json'),
                input_protocol_sha256=sha(PILOT/'protocol.json'), input_results_sha256=sha(PILOT/'results.json'),
                instrumentation='All component timers are inclusive. Top-level phases are disjoint; nested timers must not be summed with parents.',
                upstream_scope='For each consumed manifest once per case: read_model_batch plus bound_model for all emitted SAT rows (_batch layer), then read_model_batch plus bound_model for every matching saved SAT candidate receipt (solve layer). This replays the two model-binding layers, not solver execution or unrelated proof bookkeeping.',
                validation_overhead='Reference validation independently reevaluates the original combinational AIG at each saved unique sample and compares the whole returned sample vector; this extra test-only pass is separately timed and included in primary wall.',
                cold_scope='Fresh process, Graph, immutable snapshot and cone-plan cache in each trial. OS file cache is not flushed.',
                stop_policy='First integrity, semantic, capacity or timeout failure stops all remaining trials; no automatic resume/retry.')
    plan['capacity_at_freeze'] = capacity_check(plan)
    write(ROOT/'plan.json', plan)
    write(ROOT/'ledger.json', dict(status='NOT_STARTED', plan_sha256=sha(ROOT/'plan.json'),
          trials=[dict(t, status='NOT_STARTED') for t in proposal['trials']]))
    print(json.dumps(dict(status='FROZEN', plan_sha256=sha(ROOT/'plan.json'), harness_sha256=sha(__file__),capacity=plan['capacity_at_freeze'])), flush=True)

class Timers:
    def __init__(self): self.seconds=Counter(); self.calls=Counter()
    @contextmanager
    def region(self, name):
        start=time.perf_counter()
        try: yield
        finally: self.seconds[name]+=time.perf_counter()-start; self.calls[name]+=1
    def wrap(self, obj, name, label):
        original=getattr(obj,name)
        def wrapped(*args,**kwargs):
            with self.region(label): return original(*args,**kwargs)
        setattr(obj,name,wrapped)


def comparable(rows):
    rows=copy.deepcopy(rows)
    for row in rows: row.pop('source_provenance_sha256',None)
    return rows

def sample_keys(rows, count):
    index={}
    for row in rows: index.setdefault(row['sample_index'], tuple(row['current_inputs']+row['successor_state']))
    require(set(index)==set(range(count)), 'sample index mismatch')
    return [index[i] for i in range(count)]

def worker(trial_index):
    start=time.monotonic(); plan=read(ROOT/'plan.json'); trial=plan['proposal']['trials'][trial_index]
    out=ROOT/'trials'/f"trial_{trial_index:02d}_{Path(trial['case']).stem}_{trial['validator']}"
    require(not out.exists(),'trial output already exists');out.mkdir(parents=True)
    timings=Timers(); p=None
    try:
        with timings.region('top_case_guard'):
            require(sha(__file__)==plan['harness_sha256'],'harness changed')
            source_check(); capacity_check(plan)
            for name,value in plan['proposal']['environment'].items(): require(os.environ.get(name)==value,'environment mismatch '+name)
            require(sha(PILOT/'protocol.json')==plan['input_protocol_sha256'],'pilot protocol drift')
            require(sha(PILOT/'results.json')==plan['input_results_sha256'],'pilot results drift')
            require(sha(CORRECT/'frozen-records/results.json')==plan['reference_results_sha256'],'reference results drift')
            case=plan['cases'][trial['case']]; directory=Path(case['directory'])
            for path,expected in case['selection_reference_hashes'].items(): require(sha(path)==expected,'selection/reference drift '+path)
            job=read(directory/'job.json')
            require(sha(job['case']['input'])==job['case']['input_sha256'],'input drift')
            require(sha(job['solver'])==job['solver_sha256'],'recorded solver bytes drift')
            for name,expected in job['source_hashes'].items(): require(sha(PILOT/'frozen_package'/name)==expected,'recorded source drift '+name)
        with timings.region('top_case_initialization'):
            sys.path.insert(0,str(SOURCE/'nonlinear_divisors'))
            import inline_models as im
            import image_guided as ig
            import prototype as p
            from anytime import Budget
            require(Path(im.__file__).resolve()==SOURCE/'nonlinear_divisors/inline_models.py','wrong runtime import')
            for module in list(sys.modules.values()):
                path=getattr(module,'__file__',None)
                if path and '/stran2' in str(path) and Path(path).suffix=='.py' and Path(path).resolve()!=Path(__file__).resolve():
                    require(Path(path).resolve().is_relative_to(SOURCE),'non-frozen STRAN2 import '+str(path))
            # Hard prohibition applies after imports and before any domain work.
            def forbidden(*args,**kwargs): raise AssertionError('saved-record worker forbids every subprocess/solver')
            subprocess.run=forbidden;subprocess.Popen=forbidden;subprocess.call=forbidden;os.system=forbidden
            deadline=Budget(start,start+plan['proposal']['resources']['per_trial_timeout_seconds'])
            a=p.Aiger(Path(job['case']['input']));graph,base,step,reset=p.compile_graph(a);config=p.Config(**job['config'])
            (_,image,initial),_=p.signatures(graph,[base,step,reset],config)
            seq=[image[i]|(initial[i]<<config.lanes) for i in range(a.m+1)];mask=(1<<(2*config.lanes))-1
            seen={tuple((seq[node]>>lane)&1 for node in range(1,1+a.ni+a.nl)) for lane in range(mask.bit_length())}
            roots=[json.loads(line) for line in (directory/'root_search.jsonl').read_text().splitlines()]
            root_group={r['root']:i//job['chunk_roots'] for i,r in enumerate(roots)}
            roles,variables=im.d.projected_pis(graph,base,step,a)
            expected=dict(input_sha256=job['case']['input_sha256'],source_hashes=job['source_hashes'],solver_sha256=job['solver_sha256'],roles=roles,variables=variables)
            candidate_cache={};upstream_seen=set();round_results=[];model_count=accepted_count=0;counts=Counter()
            timings.wrap(im,'read_model_batch','nested_binding_read_hash_parse')
            timings.wrap(im,'bound_model','nested_binding_receipt')
            timings.wrap(im,'graph_cnf_sha256','nested_compiled_cnf_hash')
            timings.wrap(im.ConeValidator,'__init__','nested_cone_capture_including_cnf_hash')
            timings.wrap(im.ConeValidator,'plan','nested_cone_plan')
            timings.wrap(im.ConeValidator,'evaluate','nested_cone_evaluate_including_plan')
            timings.wrap(im.d,'graph_values','nested_full_compiled_evaluate')
            timings.wrap(a,'step','nested_original_AIG_step')
            timings.wrap(p,'recipe_eval','nested_original_recipe')
            timings.wrap(p,'write_json','nested_runtime_JSON_output')
        for round_spec in case['rounds']:
            deadline.remaining()
            with timings.region('top_round_prepare'):
                saved=Path(round_spec['saved']);reference=Path(round_spec['reference'])
                stored=read(saved/'replayed_models.json');refinement=read(saved/'refinement.json')
                refdiff=read(reference/'differential.json');refrows=read(reference/'full/replayed_models.json')
                require(sha(saved/'replayed_models.json')==refdiff['source_replayed_models_sha256'] and sha(saved/'refinement.json')==refdiff['source_refinement_sha256'],'saved differential source mismatch')
                require(sha(reference/'full/replayed_models.json')==refdiff['full_replayed_models_sha256'],'full reference mismatch')
                require(refinement['model_report']['model_cache_misses']==0,'unexpected historical cache miss')
                sources=[]
                for model in stored:
                    chunk=model['source_chunk']
                    if chunk not in candidate_cache: candidate_cache[chunk]=read(directory/'chunks'/chunk/'candidates.json')
                    sources.append(copy.deepcopy(candidate_cache[chunk][model['source_proof_candidate_index']]))
                groups={root_group[c['root']] for c in sources};require(len(groups)==1,'mixed root groups');group=next(iter(groups))
                selected_roots=[dict(root=r['root'],pool=r['pool'],pool_info=r['pool_info']) for r in roots[group*job['chunk_roots']:(group+1)*job['chunk_roots']]]
                round_out=out/round_spec['name'];round_out.mkdir()
                identity=dict(teacher_version_before=refinement['teacher_version_before'],added_domain=ig.DOMAIN,pool_signature_sha256=refinement['pool_signature_sha256'])
            with timings.region('top_upstream_binding_layers'):
                # _batch validates every emitted SAT row; solve validates every
                # corresponding candidate receipt including exact cache reuse.
                for candidate in sources:
                    cert=candidate['anytime_certificate'];receipt=cert['receipts']['step'];ref=receipt['inline_image_model']
                    key=(cert['chunk'],ref['manifest_file'],ref['manifest_sha256'])
                    if key in upstream_seen: continue
                    chunk=directory/'chunks'/cert['chunk'];binding=dict(expected,cnf_sha256=cert['cnf_sha256'])
                    batch=im.read_model_batch(chunk,ref,binding)
                    manifest,queries,results,models=batch
                    for model_index,model in enumerate(models):
                        row=model['query']
                        synthetic=dict(cnf_sha256=manifest['cnf_sha256'],assumptions=queries[row][2:],row=row,result='SAT',
                            queries_file=manifest['artifacts']['queries']['file'],queries_sha256=manifest['artifacts']['queries']['sha256'],
                            results_file=manifest['artifacts']['results']['file'],results_sha256=manifest['artifacts']['results']['sha256'])
                        im.bound_model(synthetic,dict(ref,model_row=model_index),batch);counts['upstream_batch_model_rows']+=1
                    batch=im.read_model_batch(chunk,ref,binding)
                    for c in candidate_cache[cert['chunk']]:
                        r=c['anytime_certificate']['receipts'].get('step',{});m=r.get('inline_image_model')
                        if m and (m['manifest_file'],m['manifest_sha256'])==key[1:]:
                            im.bound_model(r,m,batch);counts['upstream_solve_model_receipts']+=1
                    upstream_seen.add(key);counts['upstream_batches_each_layer']+=1
            with timings.region('top_collector'):
                samples,report=im.collect_inline_models(a,graph,base,step,sources,round_out/'models',dict(job,inline_cone_check=trial['validator']=='cone'),deadline,identity)
            with timings.region('top_reference_validation'):
                rows=read(round_out/'models/replayed_models.json')
                require(comparable(rows)==comparable(stored)==comparable(refrows),'model witness mismatch')
                keys=sample_keys(rows,len(samples));reference_samples=[None]*len(samples)
                for row in refrows:
                    index=row['sample_index']
                    if reference_samples[index] is not None: continue
                    # Test-only direct original combinational evaluation. It is
                    # measured separately, never substituted for runtime replay.
                    values=[0]+row['current_inputs']+row['successor_state']
                    for x,y in a.gates: values.append((values[x//2]^(x&1))&(values[y//2]^(y&1)))
                    reference_samples[index]=values
                require(samples==reference_samples,'whole original sample-vector mismatch')
                require(report['queries']==report['additional_solver_queries']==0,'unexpected solver query')
                sample_sha=digest(samples)
            with timings.region('top_admission_signature'):
                added,decisions=ig.select_new_samples(selected_roots,seq,mask,samples,keys,seen)
                require(decisions==refinement['decisions'] and len(added)==refinement['accepted_samples'],'projection admission mismatch')
                if added: seq,mask=im.d.append_samples(seq,mask,added)
                signature=ig.signature_hash(seq,mask)
                require(mask.bit_length()==refinement['construction_signature_bits'] and signature==refinement['construction_signature_sha256'],'construction signature mismatch')
            with timings.region('top_round_output'):
                counts.update(report.get('cone_validation',{}));model_count+=len(stored);accepted_count+=len(added)
                result=dict(round=round_spec['name'],models=len(stored),unique_samples=len(samples),accepted_samples=len(added),samples_sha256=sample_sha,
                    construction_signature_sha256=signature,decisions_sha256=digest(decisions),witness_semantics_sha256=digest(comparable(rows)),
                    same_full_saved_reference=True,model_report=report)
                write(round_out/'admission.json',dict(decisions=decisions,accepted_samples=len(added),construction_signature_sha256=signature,construction_signature_bits=mask.bit_length()))
                write(round_out/'validation.json',result);round_results.append(result)
        with timings.region('top_final_guard'):
            source_check();require(sha(__file__)==plan['harness_sha256'],'harness final drift')
            require(sha(job['solver'])==job['solver_sha256'],'recorded solver final drift')
            require(sha(job['case']['input'])==job['case']['input_sha256'],'original input final drift')
            capacity_check(plan)
            require(model_count==case['expected']['models'] and len(round_results)==case['expected']['rounds'] and accepted_count==case['expected']['accepted_samples'],'final coverage mismatch')
            require(timings.calls['nested_original_AIG_step']==2*model_count,'both original AIG passes required')
            require(timings.calls['nested_original_recipe']==model_count,'every original recipe required')
        summary=dict(status='PASS',trial=trial,models=model_count,rounds=len(round_results),accepted_samples=accepted_count,counts=dict(counts),
            semantic_digest=digest([{k:r[k] for k in ['round','models','unique_samples','accepted_samples','samples_sha256','construction_signature_sha256','decisions_sha256','witness_semantics_sha256']} for r in round_results]),
            new_solver_queries=0,new_DSEC=0,source_manifest_sha256=SOURCE_SHA,harness_sha256=sha(__file__),
            timers_inclusive_seconds=dict(timings.seconds),timer_calls=dict(timings.calls),worker_wall_before_summary_s=time.monotonic()-start,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,complete_sample_and_projection_reference_match=True,
            notes='Primary direct-child wall includes startup/final summary/exit. Test-only whole-sample reference reevaluation is top_reference_validation; top_collector retains exactly two original passes per model. No OS cache flush.')
        write(out/'summary.json',summary);print(json.dumps(summary),flush=True)
    except BaseException as error:
        write(out/'failure.json',dict(status='FAIL',trial=trial,error=repr(error),traceback=traceback.format_exc(),timers=dict(timings.seconds),elapsed_s=time.monotonic()-start))
        raise

def run():
    plan=read(ROOT/'plan.json');ledger=read(ROOT/'ledger.json')
    require(ledger['status']=='NOT_STARTED','no retry/resume of started experiment')
    require(sha(ROOT/'plan.json')==ledger['plan_sha256'] and sha(__file__)==plan['harness_sha256'],'frozen harness/plan drift')
    source_check();capacity_check(plan);env=dict(os.environ,**plan['proposal']['environment'])
    ledger.update(status='RUNNING',started_utc=utc(),controller_pid=os.getpid());write(ROOT/'ledger.json',ledger)
    print(json.dumps(dict(event='START',utc=utc(),plan_sha256=ledger['plan_sha256'],capacity=capacities())),flush=True)
    active=None
    try:
        for trial in ledger['trials']:
            before=capacity_check(plan);require(sha(__file__)==plan['harness_sha256'],'harness drift')
            require(sha(ROOT/'plan.json')==ledger['plan_sha256'],'plan drift')
            index=trial['trial'];command=[sys.executable,str(Path(__file__).resolve()),'worker',str(index)]
            trial.update(status='RUNNING',started_utc=utc(),command=command,capacity_before=before);write(ROOT/'ledger.json',ledger)
            log=ROOT/f'trial_{index:02d}.log';lowest=dict(before)
            done=threading.Event();monitor_errors=[]
            with log.open('w') as stream:
                start=time.monotonic()
                active=subprocess.Popen(command,stdout=stream,stderr=subprocess.STDOUT,env=env,start_new_session=True)
                child=active
                def monitor():
                    try:
                        while not done.wait(.5):
                            current=capacity_check(plan)
                            for key in lowest: lowest[key]=min(lowest[key],current[key])
                            require(time.monotonic()-start<=plan['proposal']['resources']['per_trial_timeout_seconds'],'trial direct-child timeout')
                    except BaseException as error:
                        monitor_errors.append(repr(error))
                        try: os.killpg(child.pid,signal.SIGTERM)
                        except ProcessLookupError: pass
                watcher=threading.Thread(target=monitor,daemon=True);watcher.start()
                code=child.wait()
                wall=time.monotonic()-start
                done.set();watcher.join();active=None
            trial.update(direct_child_wall_s=wall)
            require(not monitor_errors,'resource/timeout monitor: '+str(monitor_errors))
            trial.update(returncode=code,direct_child_wall_s=wall,finished_utc=utc(),capacity_low_water=lowest,log_sha256=sha(log))
            require(code==0,'trial worker nonzero exit '+str(code))
            output=ROOT/'trials'/f"trial_{index:02d}_{Path(trial['case']).stem}_{trial['validator']}"/'summary.json'
            result=read(output);require(result['status']=='PASS','trial semantic failure')
            for previous in ledger['trials']:
                if previous.get('status')=='PASS' and previous['case']==trial['case']:
                    require(previous['semantic_digest']==result['semantic_digest'],'cross-trial semantic output mismatch')
            trial.update(status='PASS',summary=str(output),summary_sha256=sha(output),semantic_digest=result['semantic_digest'],models=result['models'],rounds=result['rounds'])
            write(ROOT/'ledger.json',ledger)
            print(json.dumps(dict(event='PASS',trial=index,case=trial['case'],validator=trial['validator'],wall_s=wall,models=result['models'],rounds=result['rounds'])),flush=True)
        require(len(ledger['trials'])==24,'trial count mismatch')
        for sweep in range(2):
            for arm in ['full','cone']:
                matching=[t for t in ledger['trials'] if t['sweep']==sweep and t['validator']==arm]
                require(sum(t['models'] for t in matching)==9059 and sum(t['rounds'] for t in matching)==300,'fixed stream coverage mismatch')
        ledger.update(status='COMPLETE_ALL_24_PASS',finished_utc=utc());write(ROOT/'ledger.json',ledger)
        print(json.dumps(dict(event='COMPLETE',utc=utc(),trials=24)),flush=True)
    except BaseException as error:
        if active is not None:
            os.killpg(active.pid,signal.SIGTERM)
            try: active.wait(timeout=5)
            except subprocess.TimeoutExpired: os.killpg(active.pid,signal.SIGKILL);active.wait()
        if 'trial' in locals() and trial.get('status')=='RUNNING': trial.update(status='FAILED_OR_INTERRUPTED',error=repr(error),elapsed_s=time.monotonic()-start)
        ledger.update(status='STOPPED_FAILURE',finished_utc=utc(),error=repr(error),traceback=traceback.format_exc())
        write(ROOT/'ledger.json',ledger);raise

if __name__=='__main__':
    if sys.argv[1:] == ['prepare']: prepare()
    elif sys.argv[1:] == ['run']: run()
    elif len(sys.argv)==3 and sys.argv[1]=='worker': worker(int(sys.argv[2]))
    else: raise SystemExit('usage: timing_harness.py prepare|run|worker INDEX')
