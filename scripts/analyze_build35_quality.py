#!/usr/bin/env python3
"""Strict complete-matrix summary for the isolated Build-only fast35 study."""
import csv,collections,hashlib,json,math,re,statistics
from pathlib import Path
ROOT=Path('/mnt/home/zhaoxiran/script2/experiment_reports')
MANIFEST=Path('/mnt/home/zhaoxiran/script2/evidence/odc_build_fast35/20260909/manifest.json')
EXPECTED={x['sha256'] for x in json.loads(MANIFEST.read_text())}
BUILD='seq_build_ordered_and_gain'
def read(p):
 with p.open(newline='') as f: rows=list(csv.DictReader(f))
 if len(rows)!=35:return None
 if any(None in r or any(v is None for v in r.values()) for r in rows):raise ValueError(str(p))
 d={r['input_sha256']:r for r in rows}
 assert len(d)==35 and set(d)==EXPECTED,str(p)
 return d
def passed(r):return r['stran_status']==r['scorr_status']=='PASS' and r['error'] in ('','N/A') and r['dsec_status'] in ('SKIP','PASS')
def val(r,k):
 v=float(r[k]);assert math.isfinite(v);return v
def summarize(p,d):
 good=[r for r in d.values() if passed(r)]
 out=dict(name=p.parent.name,flow=next(iter(d.values()))['flow'],csv_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),n=35,pass_n=len(good),statuses=dict(collections.Counter(r['stran_status'] for r in d.values())),errors=[dict(file=r['file'],error=r['error'],status=r['stran_status']) for r in d.values() if not passed(r)])
 out['profile_accounting']=dict(collections.Counter(r.get('profile_accounting_complete') for r in good))
 if good:
  values=[100*val(r,BUILD)/val(r,'source_and') for r in good]
  out.update(build_mean=statistics.fmean(values),build_median=statistics.median(values),build_sum=sum(val(r,BUILD) for r in good),final_and=sum(val(r,'stran_and') for r in good),latches=sum(val(r,'stran_latches') for r in good),wall_sum_sec=sum(val(r,'stran_time_ms') for r in good)/1000,wall_max_sec=max(val(r,'stran_time_ms') for r in good)/1000)
 return out
def main():
 results=[]
 for dr in sorted(ROOT.glob('20260909_build35_*')):
  paths=[dr/'stran_current_stran2.csv',dr/'stran_current_stran.csv']
  if not all(p.exists() for p in paths):continue
  ds=[read(p) for p in paths]
  if any(d is None for d in ds):continue
  summaries=[summarize(p,d) for p,d in zip(paths,ds)]
  mismatches=[]
  for h in EXPECTED:
   if not all(passed(d[h]) for d in ds):continue
   for k in ['source_and','stran_and','stran_latches',BUILD,'seq_stage_and_gain','seq_commit_existing_and_gain','seq_commit_constant_and_gain']:
    if ds[0][h][k]!=ds[1][h][k]:mismatches.append([ds[0][h]['file'],k,ds[0][h][k],ds[1][h][k]])
  summaries[0]['flow_quality_mismatches']=mismatches
  b=re.search(r'_B(\d+)_',dr.name).group(1)
  control=ROOT/f'20260909_build35_control_B{b}_strict'/'stran_current_stran2.csv'
  base=read(control)
  pairs=[h for h in EXPECTED if passed(base[h]) and passed(ds[0][h])]
  gains=[val(ds[0][h],BUILD)-val(base[h],BUILD) for h in pairs]
  summaries[0]['paired_strict']={'n':len(pairs),'build_delta':sum(gains),'better_equal_worse':[sum(g>0 for g in gains),sum(g==0 for g in gains),sum(g<0 for g in gains)],'delta_pp':statistics.fmean([100*(val(ds[0][h],BUILD)-val(base[h],BUILD))/val(base[h],'source_and') for h in pairs]) if pairs else None}
  results.extend(summaries)
 print(json.dumps(results,indent=2))
if __name__=='__main__':main()
