"""Bounded truth-library completion, scored with exact retained source MFFC."""
import functools,json
from pathlib import Path
D=Path(__file__).resolve().parent
LIB=None
STATS=dict(calls=0,matching_templates=0,positive_templates=0,replaced_sop=0)
def library():
    global LIB
    if LIB is not None:return LIB
    raw=json.loads((D/'library.json').read_text());LIB={}
    for item in raw['cases']:
        n=item['inputs'];rows=item['records'];cols=[0]*(1<<n)
        for index,row in enumerate(rows):
            truth=row['truth'];bit=1<<index
            while truth:
                low=truth&-truth;cols[low.bit_length()-1]|=bit;truth-=low
        LIB[n]=(rows,cols,(1<<len(rows))-1)
    return LIB
@functools.lru_cache(maxsize=4096)
def matching(n,truth,care):
    rows,cols,allbits=library()[n];result=allbits
    while care and result:
        low=care&-care;k=low.bit_length()-1
        result &= cols[k] if truth&low else cols[k]^allbits
        care-=low
    return result
def choose(truth,care,leaves,a,rnodes,original):
    STATS['calls']+=1;n=len(leaves);rows,_,_=library()[n];found=matching(n,truth,care)
    STATS['matching_templates']+=found.bit_count();nci=a.ni+a.nl
    positions={v:i for i,v in enumerate(sorted(rnodes))}
    @functools.lru_cache(None)
    def retained(v):
        if v not in rnodes:return 0
        x,y=a.gates[v-nci-1];return (1<<positions[v])|retained(x//2)|retained(y//2)
    masks=[retained(v) for v in leaves]
    @functools.lru_cache(None)
    def removed(support):
        protected=0
        for j,m in enumerate(masks):
            if support>>j&1:protected|=m
        return len(rnodes)-protected.bit_count()
    recipe,out=original;support=0
    for c in list(recipe)+[out]:
        if c>=2:support |= 1<<leaves.index(c//2)
    g=len(recipe)//2;gain=removed(support)-g
    best=(-gain,g,list(recipe),out) if g>0 and g<=20 and gain>0 else None
    def mapcode(c):return 2*leaves[c//2-1]+(c&1) if c>=2 else c
    while found:
        low=found&-found;q=rows[low.bit_length()-1];found-=low
        gain=removed(q['support'])-q['gates']
        if gain<=0:continue
        STATS['positive_templates']+=1
        rr=[mapcode(c) for c in q['recipe']];oo=mapcode(q['out'])
        rank=(-gain,q['gates'],rr,oo)
        if best is None or rank<best:best=rank
    result=original if best is None else (best[2],best[3])
    STATS['replaced_sop']+=result!=original
    return result
