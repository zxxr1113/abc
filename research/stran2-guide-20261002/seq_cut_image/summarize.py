#!/usr/bin/env python3
"""Saved-result comparisons: recipe opportunity is not committed area."""
import argparse,collections,csv,hashlib,json,statistics
from pathlib import Path
D=Path(__file__).resolve().parent;E=D.parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def key(c):return c['root'],tuple(c['recipe']),c['out']
def work(path):
    out={}
    for tag in ['care','image','free']:
        p=path/(tag+'.results.csv')
        if not p.exists():out[tag]=None;continue
        rr=list(csv.DictReader(p.open()));assert [int(r['query'])for r in rr]==list(range(len(rr)))
        out[tag]=dict(observed_queries=len(rr),statuses=dict(collections.Counter(r['result']for r in rr)),conflicts=sum(int(r['conflicts'])for r in rr),solver_wall_s=sum(float(r['wall_s'])for r in rr),csv_sha256=sha(p))
    return out
def main():
    p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');args=p.parse_args();ident=read(D/('pilot_identity.json'if args.pilot else 'run_identity.json'));run=Path(ident['path']);assert(run/'complete.json').is_file();manifest=read(run/'manifest.json');rows=[]
    for c in manifest['cases']:
        row=dict(file=c['file'],family=c['family'],loaded_AND=c['source_and'],input_AND=c['input_and'],arms={})
        originals=read(E/'seq_care_cut2/diagnostic55'/Path(c['file']).stem/'result.json')
        data={}
        for mode in ['pair','full']:
            p=run/mode/Path(c['file']).stem;outcome=read(p/'outcome.json');diag=p/'diagnostic';r=dict(status='complete'if outcome['complete']else outcome['status'],returncode=outcome['returncode'],wall_s=outcome['wall_s'],outcome=str(p/'outcome.json'),outcome_sha256=sha(p/'outcome.json'),work=work(diag),positive_recipes=None,free_SAT_positive_recipes=None,selected_roots=None,overlapping_gain_potential=None)
            if outcome['complete']:
                q=read(diag/'result.json');data[mode]=q;m=q['metrics'];r.update(metrics=m,positive_recipes=len(q['candidates']),free_SAT_positive_recipes=sum(x['free_sat']==1 for x in q['candidates']),selected_roots=len(q['selected']),overlapping_gain_potential=m['overlapping_gain_potential'],result_sha256=sha(diag/'result.json'))
                if mode=='pair':
                    r['legacy_candidates_exactly_equal']=q['candidates']==originals['candidates'];r['legacy_selected_exactly_equal']=q['selected']==originals['selected']
                    assert r['legacy_candidates_exactly_equal'] and r['legacy_selected_exactly_equal'],c['file']
            row['arms'][mode]=r
        if set(data)=={'pair','full'}:
            pp={key(x):x for x in data['pair']['candidates'] if x['free_sat']==1};ff={key(x):x for x in data['full']['candidates'] if x['free_sat']==1};new=ff.keys()-pp.keys();lost=pp.keys()-ff.keys()
            row['comparison']=dict(new_exact_free_SAT_recipes=len(new),lost_exact_free_SAT_recipes=len(lost),retained_exact_free_SAT_recipes=len(ff.keys()&pp.keys()),new_exact_roots=len({k[0]for k in new}),new_root_ids=sorted({k[0]for k in ff}-{k[0]for k in pp}),selected_new_exact=sum(key(x)not in pp for x in data['full']['selected']),selected_roots_delta=len(data['full']['selected'])-len(data['pair']['selected']),overlapping_gain_delta=data['full']['metrics']['overlapping_gain_potential']-data['pair']['metrics']['overlapping_gain_potential'])
        else:row['comparison']=None
        rows.append(row)
    groups={}
    for name,rr in [('all',rows)]+[(f,[r for r in rows if r['family']==f])for f in ['discovery','holdout']]+[(n,[r for r in rows if lo<=r['loaded_AND']<hi])for n,lo,hi in [('under1k',0,1000),('1k_to_10k',1000,10000),('at_least10k',10000,10**30)]]:
        common=[r for r in rr if r['comparison']is not None];arms={}
        for mode in ['pair','full']:
            aa=[r['arms'][mode]for r in rr];arms[mode]=dict(planned=len(rr),complete=sum(x['status']=='complete'for x in aa),states=dict(collections.Counter(x['status']for x in aa)),all_attempt_wall_s=sum(x['wall_s']for x in aa),completed_positive_recipes=sum(x['positive_recipes']for x in aa if x['positive_recipes']is not None),completed_free_SAT_recipes=sum(x['free_SAT_positive_recipes']for x in aa if x['free_SAT_positive_recipes']is not None))
        groups[name]=dict(planned=len(rr),arms=arms,common_complete=len(common),new_exact_free_SAT_recipes=sum(r['comparison']['new_exact_free_SAT_recipes']for r in common),new_recipe_cases=[r['file']for r in common if r['comparison']['new_exact_free_SAT_recipes']],new_root_cases=[r['file']for r in common if r['comparison']['new_root_ids']],lost_exact_recipes=sum(r['comparison']['lost_exact_free_SAT_recipes']for r in common),overlapping_gain_delta=sum(r['comparison']['overlapping_gain_delta']for r in common))
    out=dict(status='PASS'if all(r['comparison']is not None for r in rows)else 'completed-with-incomplete-cases',scope='Offline positive recipe opportunity, not actual area or valid optimized products; overlap is never added to main metric',run=str(run),rules_sha256=ident['rules_sha256'],script_sha256=sha(__file__),groups=groups,cases=rows)
    name='pilot_summary'if args.pilot else 'final_results';(D/(name+'.json')).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    flat=[]
    for r in rows:
        for mode,x in r['arms'].items():flat.append(dict(file=r['file'],family=r['family'],loaded_AND=r['loaded_AND'],input_AND=r['input_AND'],mode=mode,**{k:x[k]for k in ['status','returncode','wall_s','positive_recipes','free_SAT_positive_recipes','selected_roots','overlapping_gain_potential']},comparison=r['comparison']))
    with(D/(name+'.csv')).open('w')as f:w=csv.DictWriter(f,list(flat[0]));w.writeheader();w.writerows(flat)
    print(json.dumps(groups,indent=2))
if __name__=='__main__':main()
