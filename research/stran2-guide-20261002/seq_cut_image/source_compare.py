#!/usr/bin/env python3
"""Post-hoc exact-identity attribution against the already frozen three-source union."""
import collections,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent;E=D.parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def key(c):return c['root'],tuple(c['recipe']),c['out']
def stage(p):
    for name,label in [('result.json','complete'),('free.results.csv','free-SAT'),('free.queries','free-SAT-prepare'),('image_proofs.json','SOP-synthesis'),('image.results.csv','full-image-SAT'),('image_plan.json','full-image-CNF-prepare'),('care_proofs.json','full-pattern-preparation'),('care.results.csv','pair-care-SAT'),('care.cnf','pair-CNF-prepare'),('coverage.json','pair-query-prepare'),('progress.json','cut-enumeration')]:
        if(p/name).exists():return label
    return 'startup'
def main():
    s=read(D/'final_results.json');rows=[]
    for r in s['cases']:
        stem=Path(r['file']).stem;prior=read(E/'care_certificate/oracle55'/stem/'result.json');old={key(x['candidate'])for x in prior['candidates']};out=dict(file=r['file'],loaded_AND=r['loaded_AND'],family=r['family'],complete=r['arms']['full']['status']=='complete',new_vs_pair=None,new_vs_old_three_source_union=None,new_vs_union_selected=None)
        p=Path(s['run'])/'full'/stem/'diagnostic';out['last_saved_stage']=stage(p)
        if out['complete']:
            q=read(p/'result.json');ss=[x for x in q['candidates']if x['free_sat']==1];new=[x for x in ss if key(x)not in old];out.update(new_vs_pair=r['comparison']['new_exact_free_SAT_recipes']if r['comparison']else None,new_vs_old_three_source_union=len(new),new_vs_union_selected=sum(key(x)not in old for x in q['selected']),new_vs_union_roots=len({x['root']for x in new}),new_identity=[dict(root=x['root'],gates=x['gates'],recipe=x['recipe'],out=x['out'],conservative_gain=x['conservative_gain'])for x in new],full_result_sha256=sha(p/'result.json'),prior_oracle_sha256=sha(E/'care_certificate/oracle55'/stem/'result.json'))
            if r['comparison'] is not None:
                pp=read(Path(s['run'])/'pair'/stem/'diagnostic/result.json');pa={key(x):x['free_sat']for x in pp['candidates']};fa={key(x):x['free_sat']for x in q['candidates']}
                assert all(not(pa[k] and fa[k])or pa[k]==fa[k]for k in pa.keys()&fa.keys()),'same exact recipe has contradictory free-SAT verdict'
                out['pair_SAT_disposition']=dict(collections.Counter('not-generated'if k not in fa else 'full-free-UNKNOWN'if fa[k]==0 else 'retained-free-SAT'for k,v in pa.items()if v==1))
        rows.append(out)
    groups={}
    for name,rr in [('all55',rows),('at_least10k',[r for r in rows if r['loaded_AND']>=10000]),('at_least10k_excluding_mem_b17',[r for r in rows if r['loaded_AND']>=10000 and r['file']not in ['045_mem_ctrl.aig','031_b17.aig','032_b17_opt.aig']])]:
        cc=[r for r in rr if r['complete']];groups[name]=dict(planned=len(rr),complete=len(cc),new_vs_union=sum(r['new_vs_old_three_source_union']for r in cc),selected_new_vs_union=sum(r['new_vs_union_selected']for r in cc),cases_with_new=[r['file']for r in cc if r['new_vs_old_three_source_union']],timeout_stages=dict(collections.Counter(r['last_saved_stage']for r in rr if not r['complete'])))
    out=dict(status='PASS',script_sha256=sha(__file__),source_summary_sha256=sha(D/'final_results.json'),groups=groups,cases=rows,interpretation='Exact syntax identity is bound to the same immutable original AIG. New recipe counts are opportunities only, not committed AND. The prior universe contains all original cut2/PDR3/GlobalRO exact recipes, not merely selected candidates. Absence here says nothing about native candidates never exported.')
    (D/'source_comparison.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(groups,indent=2))
if __name__=='__main__':main()
