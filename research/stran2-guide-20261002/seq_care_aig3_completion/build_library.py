#!/usr/bin/env python3
"""Enumerate all connected <=3 AND shapes; no benchmark inputs or solver."""
import collections, hashlib, itertools, json, time
from pathlib import Path
D=Path(__file__).resolve().parent
def variables(n):
    width=1<<n
    return [sum(((1<<(1<<j))-1)<<p for p in range(1<<j,width,2<<j)) for j in range(n)],(1<<width)-1
def build(n):
    start=time.monotonic();vv,mask=variables(n)
    lits=[(2*(i+1)+p,t^(mask if p else 0),1<<i) for i,t in enumerate(vv) for p in [0,1]]
    bases=[]
    for x,y in itertools.combinations(lits,2):
        if x[0]//2==y[0]//2:continue
        bases.append(((x[0],y[0]),x[1]&y[1],x[2]|y[2]))
    excluded={0,mask,*vv,*[v^mask for v in vv]};best={};attempts=collections.Counter()
    def put(recipe,truth,support):
        g=len(recipe)//2;attempts[g]+=2
        for p in [0,1]:
            tt=truth^(mask if p else 0)
            if tt in excluded:continue
            out=-2*g-p;rank=(g,recipe,out);key=(tt,support)
            if key not in best or rank<best[key]:best[key]=rank
    for gate0,t0,s0 in bases:
        put(gate0,t0,s0)
        for p0 in [0,1]:
            c0=-2-p0;v0=t0^(mask if p0 else 0)
            for leaf,tleaf,sleaf in lits:
                recipe2=gate0+tuple(sorted((c0,leaf)));t1=v0&tleaf;s1=s0|sleaf
                put(recipe2,t1,s1)
                for p1 in [0,1]:
                    c1=-4-p1;v1=t1^(mask if p1 else 0)
                    for leaf2,tleaf2,sleaf2 in lits:
                        put(recipe2+tuple(sorted((c1,leaf2))),v1&tleaf2,s1|sleaf2)
                    for q0 in [0,1]:
                        put(recipe2+tuple(sorted((c1,-2-q0))),v1&(t0^(mask if q0 else 0)),s1)
    for i,(gate0,t0,s0) in enumerate(bases):
        for gate1,t1,s1 in bases[i:]:
            for p0,p1 in itertools.product([0,1],repeat=2):
                recipe3=gate0+gate1+tuple(sorted((-2-p0,-4-p1)))
                put(recipe3,(t0^(mask if p0 else 0))&(t1^(mask if p1 else 0)),s0|s1)
    records=[dict(truth=t,support=s,gates=g,recipe=list(r),out=o) for (t,s),(g,r,o) in sorted(best.items())]
    # Independent full truth evaluation checks every representative and its actual syntactic support.
    for q in records:
        built=[];used=0
        def ev(c):
            nonlocal used
            if c>=0:
                used |= 1<<(c//2-1);return vv[c//2-1]^(mask if c&1 else 0)
            z=-c-2;assert z//2<len(built);return built[z//2]^(mask if z&1 else 0)
        for x,y in zip(q['recipe'][::2],q['recipe'][1::2]):built.append(ev(x)&ev(y))
        assert ev(q['out'])==q['truth'] and used==q['support']
    return dict(inputs=n,records=records,stats=dict(records=len(records),truths=len({r['truth'] for r in records}),
                 gates=dict(collections.Counter(r['gates'] for r in records)),enumerated_templates=dict(attempts),wall_s=time.monotonic()-start))
def main():
    assert not (D/'library.json').exists()
    result=dict(schema=1,scope='Canonical minimum-gate representative per exact truth and syntactic support among every connected <=3-AND DAG shape. Edge/output negation allowed; constants/direct truth functions excluded.',
                shape_classes=['one gate','two-gate chain','three-gate chain','three-gate chain reusing gate0 at output','two parallel gates combined by output gate'],
                cases=[build(n) for n in range(2,7)])
    p=D/'library.json';p.write_text(json.dumps(result,separators=(',',':'))+'\n')
    stats=dict(script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),library_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size,cases=[r['stats']|{'inputs':r['inputs']} for r in result['cases']])
    (D/'library_stats.json').write_text(json.dumps(stats,indent=2,sort_keys=True)+'\n');print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
