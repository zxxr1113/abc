"""Preparation-only audit helpers; imports the frozen diagnostic, never changes it."""
from __future__ import annotations
import importlib.util
import json
from pathlib import Path
import random
import sys
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
FRONTIER=PACKAGE/'unsampled_frontier_diagnostic'
sys.path.insert(0,str(FRONTIER))
from common import Bindings, Deadline, authenticate, cid, digest, load_runtime, read, require, sha, write_new
from independent_aig import Aig as IndependentAig, recipe as independent_recipe
import common as frontier_common
require(Path(frontier_common.__file__).resolve()==FRONTIER/'common.py','wrong diagnostic common module')

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def source_manifest():
    return {p.name:sha(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.suffix in ('.py','.json','.md')
            and p.name not in ('source_manifest.json','validation.json')}

def audit_dependencies():
    # The whole-original hash and Direct grammar are established, separately
    # reviewed helpers; every future audit binds their exact source bytes.
    paths=[PACKAGE/'global_expression_review/review.py',PACKAGE/'nonlinear_divisors/hash_direct_audit.py']
    return {str(p.resolve()):sha(p) for p in paths}

def verify_candidate(p,s,ia,c):
    cost=s.cost(c['root'],c['recipe'],c['out'])
    require(all(c[k]==v for k,v in cost.items()),'candidate retention cost changed')
    require(cost['conservative_gain']>0,'nonpositive source Build')
    require(p.normalize(s,c['root'],c['recipe'],c['out'])==(c['recipe'],c['out']),'source Build not normalized')
    require(c['recipe'] and all(0<n<c['root'] for n in p.external_nodes(c['recipe'],c['out'])),'source Build invalid/cyclic')
    w=c['free_witness'];values=ia.values(w['inputs'],w['state'])
    require((values[c['root']],independent_recipe(c['recipe'],c['out'],values))==(w['root'],w['replacement']) and
            w['root']!=w['replacement'],'source full free witness does not replay')
    return True

def classify(original,s,c):
    value,built,fresh,live=original.recipe(c['recipe'],c['out'])
    aliases=original.original_aliases(value)
    safe=[lit for lit in aliases if c['root'] not in s.tfi([lit//2])]
    require(not aliases or safe,'only root-dependent output aliases')
    return dict(candidate_id=[c['root'],c['recipe'],c['out']],original_output_aliases=aliases,
                safe_original_aliases=safe,later_safe_original_aliases=[x for x in safe if x//2>c['root']],
                global_live_fresh_gates=len(live),global_fresh_nodes=sorted(live))

def genuine_ids(selected,realization,classifications):
    real={r['root']:r for r in realization}
    require(len(real)==len(selected),'selected realization cardinality differs')
    result=set()
    for c in selected:
        if not c['recipe']:continue
        r=real[c['root']];record=classifications[cid(c)]
        if r['output_is_new'] and r['output_is_live'] and r['live_created_gates']>0 and not record['safe_original_aliases']:
            require(record['global_live_fresh_gates']>0,'genuine Build has no global live fresh gate')
            result.add(cid(c))
    return result

def removal_sets(selected,realization,classifications,newids):
    genuine=genuine_ids(selected,realization,classifications)
    return dict(full=list(selected),without_new_identities=[c for c in selected if cid(c) not in newids],
        without_all_genuine=[c for c in selected if cid(c) not in genuine],
        without_new_genuine=[c for c in selected if cid(c) not in newids&genuine]),genuine

def replay_independent(ia,selected,path,global_module,original_path,worlds=128):
    pa=IndependentAig(path)
    require((ia.ni,ia.nl,ia.no)==(pa.ni,pa.nl,pa.no),'product interface mismatch')
    replace={c['root']:c for c in selected};require(len(replace)==len(selected),'duplicate root')
    dependencies={c['root']:set(code//2 for code in c['recipe']+[c['out']] if code>=2) for c in selected}
    # A separate decoder and dependency checker include every original node.
    ga=global_module.Aig(original_path)
    require(not global_module.acyclic(ga,dependencies),'replacement dependency cycle')
    rng=random.Random(2026100214)
    for _ in range(worlds):
        inputs=[rng.randrange(2) for _ in range(ia.ni)];state=[rng.randrange(2) for _ in range(ia.nl)]
        values=[0]+inputs+state
        for node,(x,y) in enumerate(ia.gates,ia.ni+ia.nl+1):
            if node in replace:v=independent_recipe(replace[node]['recipe'],replace[node]['out'],values)
            else:v=(values[x//2]^(x&1))&(values[y//2]^(y&1))
            values.append(v)
        expected=[values[x//2]^(x&1) for x in ia.outputs+ia.latches]
        actual=pa.values(inputs,state)
        require(expected==[actual[x//2]^(x&1) for x in pa.outputs+pa.latches],'all-CO substitution/product replay differs')
    return dict(status='PASS',worlds=worlds,all_PO_RI=True,
        comparison='Exact original-node substitutions versus decoded product; not original/product unrestricted equality')

def direct_scope(p,s,hashdirect,selections,pools,max_gates):
    selected_union={cid(c):c for chosen in selections.values() for c in chosen}
    byroot={}
    for c in selected_union.values():byroot.setdefault(c['root'],[]).append(c)
    candidates=[];scope=[]
    for root,cs in sorted(byroot.items()):
        used=set().union(*(p.external_nodes(c['recipe'],c['out']) for c in cs))
        ordinary={0,1}|{2*n+b for n in set(pools[root])|used for b in (0,1)}
        raw=hashdirect.collect_hash_direct(s,root,pools[root],max_gates)
        for lit,w in raw.items():require(p.normalize(s,root,w['recipe'],w['out'])==([],lit),'hash Direct witness differs')
        literals=sorted(ordinary|set(raw))
        scope.append(dict(root=root,pool=pools[root],used_divisors=sorted(used),literals=literals,
                          hash_extras=sorted(set(raw)-ordinary),grammar_witnesses=raw))
        for lit in literals:candidates.append(dict(root=root,recipe=[],out=lit,**s.cost(root,[],lit),audit_origin='shared_bounded_Direct'))
    require(len(candidates)==len({cid(c) for c in candidates}),'duplicate shared Direct identity')
    return candidates,scope

def bind_reviewed_run(final_review,source,bindings):
    """Require the exact run bytes checked by the independent terminal reviewer."""
    source=Path(source).resolve();ledgers=[]
    for path,expected in final_review['evidence'].items():
        bindings.add(path,expected)
        if Path(path).suffix=='.json':
            value=read(path)
            if isinstance(value,dict) and 'run_bindings' in value:ledgers.append(value)
    require(len(ledgers)==1 and ledgers[0]['status']=='PASS','missing/ambiguous reviewed run ledger')
    ledger=ledgers[0]
    require(ledger['source_manifest_sha256']==final_review['source_manifest_sha256'] and
            ledger['original_run_files']==len(ledger['run_bindings']),'terminal source/ledger count differs')
    require(all(Path(path).resolve().is_relative_to(source) for path in ledger['run_bindings']),
            'terminal ledger refers to a different run')
    for path,expected in ledger['run_bindings'].items():bindings.add(path,expected)
    actual={str(path.resolve()) for path in source.rglob('*') if path.is_file()}
    require(actual==set(ledger['run_bindings']),'reviewed run file set changed')
    return ledger
