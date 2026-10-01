#!/usr/bin/env python3
"""Pair already verified incumbent attributions under one identical audit policy."""
import argparse
import hashlib
import json
from pathlib import Path


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())
def require(ok,message):
    if not ok:raise ValueError(message)


def stats(rows):
    count=len(rows);loaded=sum(r['loaded_and']for r in rows)
    answer=dict(cases=count)
    for label in ('baseline','refined','delta'):
        gains=[r[label+'_gain']for r in rows]
        answer[label]=dict(and_gain=sum(gains),equal_case_percent=100*sum(g/r['loaded_and']for r,g in zip(rows,gains))/count if count else None,
                          weighted_percent=100*sum(gains)/loaded if loaded else None)
    return answer


def compare(baseline,refined):
    for directory in (baseline,refined):require(read(directory/'integrity.json')['status']=='PASS','audit integrity missing')
    helpers=('audit_online_products.py','audit_products.py','diagnostic.py','hash_direct_audit.py')
    require(all(sha(baseline/'source'/name)==sha(refined/'source'/name)for name in helpers),'audit helper policy differs')
    old={r['case']:r for r in read(baseline/'results.json')};new={r['case']:r for r in read(refined/'results.json')}
    require(set(old)==set(new),'cohort differs')
    oldrun=Path(read(baseline/'plan.json')['source_run']);newrun=Path(read(refined/'plan.json')['source_run'])
    oldplan=read(oldrun/'plan.json');newplan=read(newrun/'plan.json')
    require(oldplan['config']==newplan['config'] and oldplan['chunk_roots']==newplan['chunk_roots'],'search bounds differ')
    for name in ('nonlinear_divisors/prototype.py','nonlinear_divisors/product.py','seq_cut_image/diagnose.py','teacher_adaptive_tools/teacher_bmc.py'):
        require(oldplan['runtime_source_hashes'][name]==newplan['runtime_source_hashes'][name],'graph/proof/cost runtime differs')
    rows=[]
    for case in old:
        a,b=old[case],new[case]
        require(a['input_sha256']==b['input_sha256'] and a['loaded_and']==b['loaded_and'],'input/denominator mismatch')
        require(a['validated_conditional_fresh_build_marginal']is not None and b['validated_conditional_fresh_build_marginal']is not None,'missing attribution')
        pools=[]
        for run in (oldrun,newrun):
            pools.append({r['root']:(r['pool'],r['pool_info'])for r in (json.loads(line)for line in (run/case/'root_search.jsonl').read_text().splitlines())})
        common=set(pools[0])&set(pools[1]);require(all(pools[0][root]==pools[1][root]for root in common),'common frozen pool differs')
        row=dict(case=case,input_sha256=a['input_sha256'],loaded_and=a['loaded_and'],
            baseline_gain=a['validated_conditional_fresh_build_marginal'],refined_gain=b['validated_conditional_fresh_build_marginal'],
            baseline_raw_build_gain=a['raw_build_only_gain'],refined_raw_build_gain=b['raw_build_only_gain'],
            baseline_original_search_complete=a['original_search_complete'],refined_original_search_complete=b['original_search_complete'],
            common_saved_root_pools_identical=len(common),baseline_selected_roots=a['original_selected_builds'],refined_selected_roots=b['original_selected_builds'])
        row['delta_gain']=row['refined_gain']-row['baseline_gain'];row['delta_percent']=100*row['delta_gain']/row['loaded_and'];rows.append(row)
    largest_delta=max(rows,key=lambda r:r['delta_gain'])
    largest_fraction=max(rows,key=lambda r:r['delta_gain']/r['loaded_and'])
    largest_refined_fraction=max(rows,key=lambda r:r['refined_gain']/r['loaded_and'])
    return dict(status='PASS',baseline_audit=str(baseline.resolve()),refined_audit=str(refined.resolve()),cases=rows,
        matched_policy_sha256={name:sha(baseline/'source'/name)for name in helpers},all_cases=stats(rows),
        largest_absolute_delta_case=largest_delta['case'],excluding_largest_absolute_delta=stats([r for r in rows if r is not largest_delta]),
        largest_primary_delta_case=largest_fraction['case'],excluding_largest_primary_delta=stats([r for r in rows if r is not largest_fraction]),
        largest_refined_primary_contributor=largest_refined_fraction['case'],excluding_largest_refined_primary_contributor=stats([r for r in rows if r is not largest_refined_fraction]),
        both_searches_complete=stats([r for r in rows if r['baseline_original_search_complete']and r['refined_original_search_complete']]),
        by_loaded_size={name:stats([r for r in rows if lo<=r['loaded_and']<hi])for name,lo,hi in
            [('lt1k',0,1000),('1k_to_10k',1000,10000),('10k_to_100k',10000,100000),('ge100k',100000,float('inf'))]},
        scope='same bounded selected-root Direct/hash-grammar policy on both verified incumbents; different selections remain conditional, not candidate-additive causal attribution',
        equal_transform_budget_seconds=oldplan['config']['wall_seconds'],attribution_costs_outside_transform_budget=True,
        native_novelty='NOT_CHECKED',global_direct_exhaustion=False)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--refined',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();require(not a.out.exists(),'new output file required');result=compare(a.baseline,a.refined)
    a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result['all_cases']))


if __name__=='__main__':main()
