#!/usr/bin/env python3
"""Build and independently bind v2 variable-arity safe-pattern imports; no solver runs."""
import csv,hashlib,importlib.util,json,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;E=D.parent;C=E/'care_certificate';F=E/'seq_cut_image'
sys.path.insert(0,str(C));import guide,oracle
assert Path(guide.__file__).resolve()==C/'guide.py'
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
oldprepare=module('old_prepare',C/'prepare.py');oldvalidate=module('old_validate',C/'run_family.py');oldvalidate.prepare=oldprepare;cut=module('full_cut_diagnose',F/'diagnose.py')
read=oracle.read;sha=oracle.sha;write=oracle.write;key=oracle.ident
FULL=Path(read(F/'final_results.json')['run'])
def text_sha(lines):
 h=hashlib.sha256()
 for s in lines:h.update(s.encode())
 return h.hexdigest()
def cnf_sha(g):
 def lines():
  yield f'{len(g.gates)} {1+3*sum(t is not None for t in g.gates)}\n1 1\n'
  for i,t in enumerate(g.gates):
   if t is not None:
    a,b=t;z=2*i;yield f'3 {a^1} {b^1} {z}\n2 {a} {z^1}\n2 {b} {z^1}\n'
 return text_sha(lines())
def verify_query(path,queries,expected=None):
 lines=[str(len(queries))+'\n']+[f'{i} {len(q)} '+' '.join(map(str,q))+'\n' for i,q in enumerate(queries)]
 assert sha(path.with_suffix('.queries'))==text_sha(lines)
 rows=list(csv.DictReader(path.with_suffix('.results.csv').open()))
 assert [int(r['query'])for r in rows]==list(range(len(queries)))
 answers=[int(r['result'])for r in rows];assert all(x in [-1,0,1]for x in answers)
 if expected is not None:assert answers==expected
 return answers

def verify_pair(c,a,p,g,reset,step):
 r=read(p/'care_proofs.json');assert r['metrics']['input_sha256']==c['input_sha256']
 queries=[];safe={};order=r['query_order'];assert len(order)%2==0
 for i in range(0,len(order),2):
  u,v,k,phase=order[i];assert phase=='reset' and order[i+1]==[u,v,k,'step']
  assert 0<u<v<=a.m and 0<=k<4
  for mp in [reset,step]:queries.append([mp[u]^int(not(k&1)),mp[v]^int(not(k&2))])
  if r['answers'][i:i+2]==[-1,-1]:safe[u,v]=safe.get((u,v),0)|(1<<k)
 assert sha(p/'care.cnf')==cnf_sha(g)
 verify_query(p/'care',queries,r['answers'])
 assert {(x['u'],x['v']):x['forbidden']for x in r['proven']}==safe
 return safe

def verify_full(c):
 p=FULL/'full'/Path(c['file']).stem;attempt=read(p/'outcome.json');p=p/'diagnostic'
 assert attempt['complete'] and attempt['status']=='exit' and attempt['returncode']==0
 assert attempt['input_sha256']==c['input_sha256'] and attempt['result_sha256']==sha(p/'result.json')
 a=oracle.Aiger(c['input']);g,base,step,reset=cut.compile_graph(a)
 # This also binds the inherited binary primitives to actual original CNF/queries.
 oldpairs=verify_pair(c,a,E/'seq_care_cut2/diagnostic55'/Path(c['file']).stem,g,reset,step)
 pairs=verify_pair(c,a,p,g,reset,step);assert oldpairs==pairs
 plan=read(p/'image_plan.json');proof=read(p/'image_proofs.json')
 assert plan['input_sha256']==proof['input_sha256']==c['input_sha256']
 assert proof['query_order']==plan['query_order']
 assert proof['cnf_sha256']==sha(p/'image.cnf')==cnf_sha(g)
 assert proof['queries_sha256']==sha(p/'image.queries')
 qs=[];safe={};meta=[]
 for i,pat in enumerate(plan['patterns']):
  ls=pat['leaves'];k=pat['pattern'];assert 3<=len(ls)<=6 and ls==sorted(set(ls)) and 0<min(ls)<=max(ls)<=a.m and 0<=k<(1<<len(ls))
  for phase,mp in [('reset',reset),('step',step)]:
   lits=[mp[u]^int(not(k>>j&1))for j,u in enumerate(ls)];qs.append(lits);meta.append(dict(leaves=ls,pattern=k,phase=phase,literals=lits))
  if proof['answers'][2*i:2*i+2]==[-1,-1]:safe[tuple(ls),k]=dict(leaves=ls,pattern=k,kind=0,answers=[-1,-1],query_indices=[2*i,2*i+1],path=str(p/'image_proofs.json'),sha256=sha(p/'image_proofs.json'))
 assert meta==plan['query_order'];verify_query(p/'image',qs,proof['answers'])
 declared={(tuple(r['leaves']),k)for r in proof['proven']for k in range(1<<len(r['leaves']))if r['forbidden']>>k&1};assert set(safe)==declared
 r=read(p/'result.json');free=[]
 for q in r['candidates']:
  cut.validate_recipe(q);ls=q['leaves'];vv,mask=cut.vars_tt(len(ls));memo={0:0,**dict(zip(ls,vv))}
  def evroot(l):
   u=l//2
   if u not in memo:
    assert u>a.ni+a.nl
    x,y=a.gates[u-a.ni-a.nl-1];memo[u]=evroot(x)&evroot(y)
   return memo[u]^(mask if l&1 else 0)
  assert evroot(2*q['root'])==int(q['truth'])
  care=mask
  for k in range(1<<len(ls)):
   forbidden=(tuple(ls),k)in safe or any(pairs.get((u,v),0)>>(int(bool(k>>i&1))+2*int(bool(k>>j&1)))&1 for i,u in enumerate(ls)for j,v in enumerate(ls)if i<j)
   if forbidden:care &= ~(1<<k)
  assert care==int(q['care'])
  assert q['gates']==len(q['recipe'])//2 and q['removable']-q['gates']==q['conservative_gain']>0
  built=[]
  def ev(code):
   if code>=0:assert code//2<q['root'];return base[code//2]^(code&1)
   assert code<=-2;z=-code-2;assert z//2<len(built);return built[z//2]^(z&1)
  for x,y in zip(q['recipe'][::2],q['recipe'][1::2]):built.append(g.land(ev(x),ev(y)))
  free.append([g.xor(base[q['root']],ev(q['out']))])
 assert cnf_sha(g)==sha(p/'free.cnf');verify_query(p/'free',free,[q['free_sat']for q in r['candidates']])
 files=['result.json','care_proofs.json','care.cnf','care.queries','care.results.csv','image_plan.json','image_proofs.json','image.cnf','image.queries','image.results.csv','free.cnf','free.queries','free.results.csv']
 identities={str(p/f):sha(p/f)for f in files};identities[str(p.parent/'outcome.json')]=sha(p.parent/'outcome.json')
 return r,safe,identities

def make_case(c,oldrow):
 start=time.monotonic();oldcheck=oldvalidate.validate(c,oldrow);full,safe,deps=verify_full(c)
 old=read(C/'oracle55'/Path(c['file']).stem/'result.json');union={}
 for r in old['candidates']:
  if r['full_seq_certificate']:union[key(r['candidate'])]=(r['candidate'],'old')
 for q in full['candidates']:
  if q['free_sat']==1:union.setdefault(key(q),(q,'full'))
 picked={}
 for q,source in union.values():
  rank=(-q['conservative_gain'],q['gates'],q['recipe'],q['out'])
  if q['root']not in picked or rank<picked[q['root']][0]:picked[q['root']]=(rank,q,source)
 selected=[dict(candidate=picked[root][1],source=picked[root][2])for root in sorted(picked)]
 facts=[dict(leaves=[u,v],pattern=k,**proof)for(u,v,k),proof in sorted(oldprepare.pattern_evidence(c).items())]
 cuts={tuple(x['candidate']['leaves'])for x in selected if x['source']=='full'}
 facts += [safe[k]for k in sorted(safe)if k[0]in cuts]
 a=oracle.Aiger(c['input']);lines=[f'stran-seq-care-cert-v2 {a.ni} {a.nl} {a.no} {a.na} {len(selected)}']
 lines += [f'{x} {y}'for x,y in a.gates]+list(map(str,a.outputs))+list(map(str,a.latches))
 for x in selected:
  q=x['candidate'];lines.append(' '.join(map(str,[q['root'],q['gates'],q['out'],q['removable'],*q['recipe']])))
 lines.append(str(len(facts)))
 for p in facts:lines.append(' '.join(map(str,[len(p['leaves']),*p['leaves'],p['pattern'],p['kind'],*p['answers'],p['sha256']])))
 return '\n'.join(lines)+'\n',dict(case=c,candidates=selected,primitive_evidence=facts,full_source_identities=deps,old_candidate_file=oldrow['candidate_file'],old_candidate_file_sha256=oldrow['candidate_file_sha256'],rule_sha256=sha(D/'frozen_rules.json'),universe=dict(old_certified=sum(r['full_seq_certificate']for r in old['candidates']),full_free_SAT=sum(q['free_sat']==1 for q in full['candidates']),union_exact=len(union)),validation_wall_s=time.monotonic()-start)

def validate(c,row):
 start=time.monotonic();original={r['file']:r for r in read(E/'new58_unified/inputs.json')['rows']}[c['file']]
 text,rebuilt=make_case(c,original);saved=read(row['sidecar'])
 assert sha(row['sidecar'])==row['sidecar_sha256'] and sha(row['candidate_file'])==row['candidate_file_sha256']
 assert Path(row['candidate_file']).read_text()==text
 assert all(saved[k]==v for k,v in rebuilt.items()if k!='validation_wall_s')
 return dict(file=c['file'],status='verified',wall_s=time.monotonic()-start,candidate_file_sha256=sha(row['candidate_file']),full_proofs=len(saved['primitive_evidence']),candidates=len(saved['candidates']))

def main():
 inp=read(E/'new58_unified/inputs.json');out=D/'inputs';out.mkdir(exist_ok=False);rows=[]
 oldrows={r['file']:r for r in inp['rows']};summary={r['file']:r for r in read(F/'final_results.json')['cases']}
 for c in inp['cases']:
  stem=Path(c['file']).stem
  if summary[c['file']]['arms']['full']['status']!='complete':
   rows.append(dict(file=c['file'],status='preparation-timeout',old=oldrows[c['file']],joint=None));continue
  text,s=make_case(c,oldrows[c['file']]);p=out/f'{stem}.care';p.write_text(text);s.update(candidate_file=str(p),candidate_file_sha256=sha(p));write(p.with_suffix('.json'),s)
  row=dict(file=c['file'],status='prepared',old=oldrows[c['file']],joint=dict(file=c['file'],candidate_file=str(p),candidate_file_sha256=sha(p),sidecar=str(p.with_suffix('.json')),sidecar_sha256=sha(p.with_suffix('.json'))),candidates=len(s['candidates']),new_source_selected=sum(r['source']=='full'for r in s['candidates']),full_primitive_patterns=sum(len(r['leaves'])>2 for r in s['primitive_evidence']))
  rows.append(row);print(stem,row['candidates'],row['new_source_selected'],row['full_primitive_patterns'],flush=True)
 write(D/'inputs.json',dict(cases=inp['cases'],rows=rows,missing_prefix=inp['missing_prefix'],original_population=58,old_inputs_sha256=sha(E/'new58_unified/inputs.json'),rule_sha256=sha(D/'frozen_rules.json')))
if __name__=='__main__':main()
