"""Read-only trial analysis; writes a new summary after all fixed trials pass."""
from pathlib import Path
from collections import Counter
import hashlib,json,statistics
R=Path(__file__).resolve().parent

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
 if not c:raise ValueError(m)
def write(p,v):
 require(not Path(p).exists(),'refuse summary overwrite')
 Path(p).write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
l=read(R/'ledger.json');p=read(R/'plan.json');require(l['status']=='COMPLETE_ALL_24_PASS','24 PASS required')
require(sha(R/'plan.json')==l['plan_sha256'],'plan drift');require(sha(R/'timing_harness.py')==p['harness_sha256'],'harness drift')
rows=[]
for t in l['trials']:
 require(t['status']=='PASS','failed trial')
 require(sha(t['summary'])==t['summary_sha256'],'summary drift')
 s=read(t['summary']);n=s['timers_inclusive_seconds']; c=s['timer_calls']
 compiled=(n.get('nested_full_compiled_evaluate',0)+n.get('nested_compiled_cnf_hash',0)) if t['validator']=='full' else (n.get('nested_cone_capture_including_cnf_hash',0)+n.get('nested_cone_evaluate_including_plan',0))
 original=n['nested_original_AIG_step']+n['nested_original_recipe']
 top={k:v for k,v in n.items() if k.startswith('top_')}
 rows.append(dict(trial=t['trial'],sweep=t['sweep'],case=t['case'],arm=t['validator'],models=s['models'],rounds=s['rounds'],wall_s=t['direct_child_wall_s'],
  compiled_validator_s=compiled,original_replay_s=original,collector_s=n['top_collector'],upstream_binding_s=n['top_upstream_binding_layers'],
  guard_s=n['top_case_guard']+n['top_final_guard'],initialization_s=n['top_case_initialization'],reference_validation_s=n['top_reference_validation'],
  admission_s=n['top_admission_signature'],output_s=n['top_round_output']+n.get('nested_runtime_JSON_output',0),
  collector_other_s=n['top_collector']-compiled-original-n.get('nested_runtime_JSON_output',0),
  startup_exit_unassigned_s=t['direct_child_wall_s']-sum(top.values()),top_disjoint_s=top,
  nested_inclusive_s={k:v for k,v in n.items() if k.startswith('nested_')},timer_calls=c,counts=s['counts'],semantic_digest=s['semantic_digest'],peak_rss_kib=s['peak_rss_kib']))
metrics=['wall_s','compiled_validator_s','original_replay_s','collector_s','upstream_binding_s','guard_s','initialization_s','reference_validation_s','admission_s','output_s','collector_other_s','startup_exit_unassigned_s']
paired=[]
for sweep in range(2):
 for case in p['proposal']['cases']:
  pair={r['arm']:r for r in rows if r['sweep']==sweep and r['case']==case}
  require(pair['full']['semantic_digest']==pair['cone']['semantic_digest'],'paired semantic drift')
  paired.append(dict(sweep=sweep,case=case,full_wall_s=pair['full']['wall_s'],cone_wall_s=pair['cone']['wall_s'],saved_wall_s=pair['full']['wall_s']-pair['cone']['wall_s'],
   wall_reduction_percent=100*(1-pair['cone']['wall_s']/pair['full']['wall_s']),component_full_minus_cone_s={m:pair['full'][m]-pair['cone'][m] for m in metrics}))
sweeps=[]
for sweep in range(2):
 totals={arm:{m:sum(r[m] for r in rows if r['sweep']==sweep and r['arm']==arm) for m in metrics} for arm in ['full','cone']}
 sweeps.append(dict(sweep=sweep,totals=totals,saved_wall_s=totals['full']['wall_s']-totals['cone']['wall_s'],wall_reduction_percent=100*(1-totals['cone']['wall_s']/totals['full']['wall_s'])))
totals={arm:{m:sum(r[m] for r in rows if r['arm']==arm) for m in metrics} for arm in ['full','cone']}
case_totals=[]
for case in p['proposal']['cases']:
 x={arm:sum(r['wall_s'] for r in rows if r['case']==case and r['arm']==arm) for arm in ['full','cone']}
 case_totals.append(dict(case=case,full_two_repetitions_s=x['full'],cone_two_repetitions_s=x['cone'],saved_s=x['full']-x['cone'],reduction_percent=100*(1-x['cone']/x['full'])))
summary=dict(status='COMPLETE_ALL_24_PASS_AWAITING_INDEPENDENT_TIMING_REVIEW',plan_sha256=l['plan_sha256'],harness_sha256=p['harness_sha256'],
 proposal_sha256=p['proposal_sha256'],source_manifest_sha256=p['source_manifest_sha256'],ledger_sha256=sha(R/'ledger.json'),analysis_script_sha256=sha(__file__),
 trials=24,repetitions_per_case_arm=2,models_per_sweep_arm=9059,rounds_per_sweep_arm=300,total_model_replays=36236,total_rounds=1200,new_solver_queries=0,new_DSEC=0,
 identical_full_sample_vectors_witnesses_admission_and_signatures_all_trials=True,started_utc=l['started_utc'],finished_utc=l['finished_utc'],
 totals=totals,saved_wall_s=totals['full']['wall_s']-totals['cone']['wall_s'],wall_reduction_percent=100*(1-totals['cone']['wall_s']/totals['full']['wall_s']),
 paired_sweeps=sweeps,cases=case_totals,paired_trials=paired,rows=rows,
 component_definitions=dict(compiled_validator_s='Full: exact CNF serialization hash plus full compiled evaluation. Cone: immutable capture (including exact CNF serialization hash) plus sparse evaluation (including cold plan construction).',
  collector_other_s='Collector minus compiled validator, both original AIG passes/recipe, and runtime JSON output. Includes collector artifact hashing/parsing, CNF reconstruction, witness/sample bookkeeping and instrumentation overhead.',
  upstream_binding_s='The two unchanged model-bearing read_model_batch/bound_model layers; all emitted rows and matching candidate receipts. No proof solver bookkeeping, new emission or SAT.',
  output_s='Top-level admission/reference output plus runtime collector provenance/witness/report JSON output. Nested runtime output is already inside collector.',
  reference_validation_s='Test-only whole-sample original combinational reference reevaluation and witness/receipt comparison, included in primary wall.',
  startup_exit_unassigned_s='Primary direct-child wall minus all disjoint top phases. Includes Python pre-main startup, final summary emission, interpreter exit, controller launch/wait overhead and intervals between phases.'),
 limitations=['Saved fixed-record pipeline only, not end-to-end transform speed or area gain.','Two matched order-reversed sweeps, not a statistical confidence claim.','OS file cache was not flushed; first-trial cache/startup effects are retained.','Nested timers overlap their parents; do not sum them with collector/upstream/top-level phase times.','This host/runtime was restarted before the experiment; do not compare these times directly with the earlier negative pilot.'],
 min_observed_capacity={k:min(t['capacity_low_water'][k] for t in l['trials']) for k in l['trials'][0]['capacity_low_water']})
write(R/'timing_summary.json',summary)
print(json.dumps({k:summary[k] for k in ['status','trials','saved_wall_s','wall_reduction_percent','totals','cases','min_observed_capacity']},indent=2))
