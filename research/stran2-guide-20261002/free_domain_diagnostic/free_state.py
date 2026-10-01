"""Standalone append-only free-domain state; default disabled, no runtime hooks.

The caller must first validate actual immutable CNF/query/model receipts with
its existing collector. This module checks their schema/bindings, independently
replays the original image model, and appends only (previous PI, previous RO).
It never owns or modifies seq signatures, pools, attempted or qualified sets.
"""
from __future__ import annotations
from dataclasses import dataclass,asdict
import hashlib
import json
from pathlib import Path
from typing import Mapping
from independent import Aig

FREE_DOMAIN='unrestricted_free_PI_RO'
IMAGE_DOMAIN='unrestricted_one_step_image'
INITIAL_LANES=256
MAX_ADDED_WORLDS=256
MAX_MODEL_BATCH=256

def check(condition,message):
    if not condition:raise ValueError(message)
def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)
def digest(value):return hashlib.sha256(canonical(value).encode()).hexdigest()
def file_sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def hash_string(value):return type(value) is str and len(value)==64 and all(c in '0123456789abcdef' for c in value)
def bits(values,count,label):
    check(isinstance(values,(list,tuple)) and len(values)==count,label+' incomplete')
    check(all(type(v) is int and v in (0,1) for v in values),label+' non-Boolean')
    return tuple(values)
def eval_recipe(recipe,out,values,mask=1):
    check(isinstance(recipe,(list,tuple)) and len(recipe)%2==0,'odd/invalid recipe')
    check(all(type(v) is int for v in tuple(recipe)+(out,)),'non-integer recipe')
    built=[]
    def value(code):
        if code>=0:
            check(code//2<len(values),'external literal out of range')
            return values[code//2]^(mask if code&1 else 0)
        check(code<=-2,'invalid internal literal')
        node,phase=divmod(-code-2,2);check(node<len(built),'forward internal literal')
        return built[node]^(mask if phase else 0)
    for i in range(0,len(recipe),2):built.append(value(recipe[i])&value(recipe[i+1]))
    return value(out)

@dataclass(frozen=True)
class FrozenOriginalAig:
    input_sha256:str
    ni:int
    nl:int
    gates:tuple
    latches:tuple
    outputs:tuple
    def __post_init__(self):
        check(hash_string(self.input_sha256),'invalid original input identity')
        check(type(self.ni) is int and self.ni>=0 and type(self.nl) is int and self.nl>=0,'invalid original interface')
        object.__setattr__(self,'gates',tuple(tuple(g) for g in self.gates))
        object.__setattr__(self,'latches',tuple(self.latches));object.__setattr__(self,'outputs',tuple(self.outputs))
        check(len(self.latches)==self.nl,'missing original latch function')
        for node,gate in enumerate(self.gates,self.nci+1):
            check(len(gate)==2 and all(type(v) is int and 0<=v<2*node for v in gate),'invalid original gate')
        check(all(type(v) is int and 0<=v<=2*self.m+1 for v in self.latches+self.outputs),'invalid original CO')
    @classmethod
    def from_file(cls,path,expected_sha256=None):
        before=file_sha(path)
        if expected_sha256 is not None:check(before==expected_sha256,'original input hash mismatch')
        a=Aig(path);check(file_sha(path)==before,'input changed during parsing')
        return cls(before,a.ni,a.nl,tuple(a.gates),tuple(a.latches),tuple(a.outputs))
    @property
    def nci(self):return self.ni+self.nl
    @property
    def m(self):return self.nci+len(self.gates)
    def values(self,inputs,state):
        inputs=bits(inputs,self.ni,'PI');state=bits(state,self.nl,'RO')
        values=[0]+list(inputs)+list(state)
        for node,(x,y) in enumerate(self.gates,self.nci+1):
            check(type(x) is int and type(y) is int and 0<=x<2*node and 0<=y<2*node,'non-topological original graph')
            values.append((values[x//2]^(x&1))&(values[y//2]^(y&1)))
        return tuple(values)
    def next_state(self,values):return tuple(values[x//2]^(x&1) for x in self.latches)

@dataclass(frozen=True)
class FreeConfig:
    enabled:bool=False
    max_added_worlds:int=MAX_ADDED_WORLDS
    def __post_init__(self):
        check(type(self.enabled) is bool,'enabled must be Boolean')
        check(type(self.max_added_worlds) is int and 0<=self.max_added_worlds<=MAX_ADDED_WORLDS,'global free cap must be within0..256')

@dataclass(frozen=True)
class LaneRecord:
    lane:int
    inputs:tuple
    state:tuple
    source_order:tuple
    source_query:int
    source_model_index:int
    source_candidate_id:tuple
    provenance_json:str
    normalized_model_sha256:str
    sampled_pi_field:str='previous_inputs'
    domain:str=FREE_DOMAIN

@dataclass(frozen=True)
class FreeSnapshot:
    input_sha256:str
    signatures:tuple
    mask:int
    version:int
    initial_domain_sha256:str
    records:tuple
    last_source_order:tuple|None
    @property
    def lanes(self):return self.mask.bit_length()
    @property
    def domain_sha256(self):return digest(dict(input_sha256=self.input_sha256,signatures=self.signatures,mask=self.mask))
    def to_dict(self):
        return dict(schema=1,domain=FREE_DOMAIN,input_sha256=self.input_sha256,signature_hex=[hex(x) for x in self.signatures],
                    mask_hex=hex(self.mask),version=self.version,initial_lanes=INITIAL_LANES,
                    initial_domain_sha256=self.initial_domain_sha256,domain_sha256=self.domain_sha256,
                    records=[asdict(r) for r in self.records],last_source_order=self.last_source_order)

@dataclass(frozen=True)
class AppendDecision:
    source_order:tuple
    source_query:int
    source_model_index:int
    action:str
    lane:int|None

@dataclass(frozen=True)
class AppendResult:
    status:str
    added:int
    before_version:int
    after_version:int
    decisions:tuple
    before_domain_sha256:str
    after_domain_sha256:str

@dataclass(frozen=True)
class FreeWitness:
    kind:str
    inputs:tuple
    state:tuple
    root:int
    replacement:int
    lane:int
    replay:str
    input_sha256:str
    free_version:int
    free_domain_sha256:str
    origin_json:str
    candidate_id:tuple
    def to_dict(self):return asdict(self)

@dataclass(frozen=True)
class DomainProjection:
    input_sha256:str
    ordered_nodes:tuple
    sequence_rows:frozenset
    free_rows:frozenset
    sequence_version:int
    free_version:int
    def can_reuse_search(self,earlier):
        check(self.input_sha256==earlier.input_sha256,'projection original graph identity changed')
        check(self.ordered_nodes==earlier.ordered_nodes,'frozen root/pool identity changed')
        return self.sequence_rows==earlier.sequence_rows and self.free_rows==earlier.free_rows


def project(signatures,mask,nodes):
    check(type(mask) is int and mask>0 and mask&(mask+1)==0,'invalid packed mask')
    check(all(type(v) is int and 0<=v<=mask for v in signatures),'signature outside mask')
    return frozenset(tuple((signatures[n]>>lane)&1 for n in nodes) for lane in range(mask.bit_length()))

def domain_projection(root,ordered_pool,sequence_signatures,sequence_mask,sequence_version,free_snapshot):
    pool=tuple(ordered_pool);nodes=(root,)+pool
    check(type(root) is int and 0<root<len(free_snapshot.signatures),'invalid projection root')
    check(len(pool)==len(set(pool)) and all(type(n) is int and 0<n<root for n in pool),'invalid ordered pool')
    check(len(sequence_signatures)==len(free_snapshot.signatures),'sequence/free graph dimensions differ')
    check(type(sequence_version) is int and sequence_version>=0,'invalid seq version')
    return DomainProjection(free_snapshot.input_sha256,nodes,project(tuple(sequence_signatures),sequence_mask,nodes),
                            project(free_snapshot.signatures,free_snapshot.mask,nodes),sequence_version,free_snapshot.version)

class FreeDomainState:
    """Owns only a free signature vector and immutable appended-world records.

    append_verified_models is atomic across the whole supplied batch, including
    malformed later rows and rows beyond the cap. Source order is a strictly
    increasing (proof-chunk, source-candidate, model-index) tuple across calls.
    The caller retains attempted/proved relations independently of this object.
    """
    def __init__(self,graph,initial_signatures,initial_mask,config=FreeConfig()):
        check(isinstance(graph,FrozenOriginalAig),'frozen original graph required')
        check(hash_string(graph.input_sha256),'invalid graph identity')
        check(isinstance(config,FreeConfig),'FreeConfig required')
        values=tuple(initial_signatures)
        check(initial_mask==(1<<INITIAL_LANES)-1,'initial256 free lanes required')
        check(len(values)==graph.m+1 and all(type(v) is int and 0<=v<=initial_mask for v in values),'invalid initial signatures')
        seen=set()
        for lane in range(INITIAL_LANES):
            world=tuple((values[n]>>lane)&1 for n in range(1,graph.nci+1));seen.add(world)
            actual=graph.values(world[:graph.ni],world[graph.ni:])
            check(actual==tuple((v>>lane)&1 for v in values),'initial node values were not evaluated on original AIG')
        self._graph=graph;self._config=config;self._seen=frozenset(seen)
        initial_hash=digest(dict(input_sha256=graph.input_sha256,signatures=values,mask=initial_mask))
        self._snapshot=FreeSnapshot(graph.input_sha256,values,initial_mask,0,initial_hash,(),None)
    @property
    def config(self):return self._config
    def snapshot(self):return self._snapshot
    def _validate_model(self,row):
        check(isinstance(row,Mapping),'model must be mapping')
        check(row.get('domain')==IMAGE_DOMAIN and row.get('reachable_teacher') is False and row.get('replay')=='PASS','wrong or unverified source model domain')
        check(row.get('free_pi_field','previous_inputs')=='previous_inputs','wrong free witness PI frame')
        g=self._graph
        u=bits(row.get('previous_inputs'),g.ni,'previous PI');state=bits(row.get('previous_state'),g.nl,'previous RO')
        current=bits(row.get('current_inputs'),g.ni,'current PI');successor=bits(row.get('successor_state'),g.nl,'successor RO')
        provenance=row.get('provenance');check(isinstance(provenance,Mapping),'missing provenance')
        check(provenance.get('input_sha256')==g.input_sha256,'model input binding differs')
        for key in ('source_provenance_sha256','models_sha256'):
            check(hash_string(provenance.get(key)),'missing/invalid '+key)
        order=provenance.get('source_order');check(isinstance(order,(list,tuple)) and len(order)==3 and all(type(v) is int and v>=0 for v in order),'invalid source order')
        order=tuple(order)
        for key in ('source_query','model_index','source_chunk_index','source_candidate_index'):
            check(type(provenance.get(key)) is int and provenance[key]>=0,'invalid '+key)
        check(order==(provenance['source_chunk_index'],provenance['source_candidate_index'],provenance['model_index']),'source order/provenance indices disagree')
        receipt=provenance.get('receipt');check(isinstance(receipt,Mapping),'missing exact receipt')
        for key in ('cnf_sha256','queries_sha256','results_sha256','solver_sha256'):
            check(hash_string(receipt.get(key)),'missing/invalid receipt '+key)
        check(receipt.get('result')=='SAT' and type(receipt.get('row')) is int and receipt['row']==provenance['source_query'],'wrong source SAT query binding')
        assumptions=receipt.get('assumptions');check(isinstance(assumptions,(list,tuple)) and len(assumptions)==1 and type(assumptions[0]) is int and assumptions[0]>=0,'invalid source assumptions')
        identity=provenance.get('candidate_id');check(isinstance(identity,(list,tuple)) and len(identity)==3,'missing source candidate identity')
        root,recipe,out=identity
        check(type(root) is int and g.nci<root<=g.m and isinstance(recipe,(list,tuple)) and type(out) is int,'invalid source candidate identity')
        check(all(type(x) is int for x in recipe),'invalid source recipe')
        check(all(x//2<root for x in tuple(recipe)+(out,) if x>=0),'source recipe has non-prefix original dependency')
        predvalues=g.values(u,state);check(g.next_state(predvalues)==successor,'predecessor transition replay failed')
        imagevalues=g.values(current,successor);old=imagevalues[root];new=eval_recipe(recipe,out,imagevalues)
        check(old!=new,'saved image model does not refute source relation')
        if 'root_value' in row:check(type(row['root_value']) is int and row['root_value']==old,'saved source root value differs')
        if 'recipe_value' in row:check(type(row['recipe_value']) is int and row['recipe_value']==new,'saved source recipe value differs')
        normalized=dict(domain=IMAGE_DOMAIN,previous_inputs=u,previous_state=state,current_inputs=current,successor_state=successor,
                        root_value=old,recipe_value=new,provenance=dict(provenance))
        source_json=canonical(dict(provenance));model_hash=digest(normalized)
        return u,state,order,provenance['source_query'],provenance['model_index'],(root,tuple(recipe),out),source_json,model_hash
    def append_verified_models(self,rows):
        before=self._snapshot;before_hash=before.domain_sha256
        if not self._config.enabled:
            return AppendResult('DISABLED',0,before.version,before.version,(),before_hash,before_hash)
        # Consume and validate the complete batch before any state mutation.
        check(isinstance(rows,(list,tuple)) and len(rows)<=MAX_MODEL_BATCH,'ordered model batch must contain at most256 rows')
        prepared=[];last=before.last_source_order
        for row in rows:
            model=self._validate_model(row);order=model[2]
            check(last is None or order>last,'source models are not in strictly increasing canonical order')
            last=order;prepared.append(model)
        seen=set(self._seen);signatures=list(before.signatures);records=list(before.records);decisions=[];added=0
        for u,state,order,query,index,identity,provenance,model_hash in prepared:
            world=u+state
            if world in seen:
                decisions.append(AppendDecision(order,query,index,'EXACT_FREE_WORLD_DUPLICATE',None));continue
            if len(records)>=self._config.max_added_worlds:
                decisions.append(AppendDecision(order,query,index,'GLOBAL_FREE_CAP_REACHED',None));continue
            lane=INITIAL_LANES+len(records);values=self._graph.values(u,state)
            for node,value in enumerate(values):signatures[node]|=value<<lane
            seen.add(world);records.append(LaneRecord(lane,u,state,order,query,index,identity,provenance,model_hash))
            decisions.append(AppendDecision(order,query,index,'APPEND_PREDECESSOR_FREE_WORLD',lane));added+=1
        mask=(1<<(INITIAL_LANES+len(records)))-1
        check(all((new&before.mask)==old for new,old in zip(signatures,before.signatures)),'old free lanes changed')
        after=FreeSnapshot(before.input_sha256,tuple(signatures),mask,before.version+int(added>0),before.initial_domain_sha256,tuple(records),last)
        # Atomic commit. Even replay/serialization errors above leave both untouched.
        self._snapshot=after;self._seen=frozenset(seen)
        return AppendResult('APPENDED' if added else 'NO_NEW_FREE_WORLD',added,before.version,after.version,tuple(decisions),before_hash,after.domain_sha256)
    def witness(self,root,recipe,out,lane=None,snapshot=None):
        snap=self._snapshot if snapshot is None else snapshot
        check(snap.input_sha256==self._graph.input_sha256,'witness snapshot graph differs')
        check(type(root) is int and self._graph.nci<root<=self._graph.m,'invalid witness root')
        check(all(type(x) is int and (x<0 or x//2<root) for x in tuple(recipe)+(out,)),'witness recipe not prefix-safe')
        difference=eval_recipe(recipe,out,snap.signatures,snap.mask)^snap.signatures[root]
        check(difference!=0,'no sampled free witness')
        if lane is None:lane=(difference&-difference).bit_length()-1
        check(type(lane) is int and 0<=lane<snap.lanes and (difference>>lane)&1,'invalid/non-witness lane')
        world=tuple((snap.signatures[n]>>lane)&1 for n in range(1,self._graph.nci+1));inputs=world[:self._graph.ni];state=world[self._graph.ni:]
        values=self._graph.values(inputs,state);check(values==tuple((v>>lane)&1 for v in snap.signatures),'witness full-world replay failed')
        old=values[root];new=eval_recipe(recipe,out,values);check(old!=new,'witness difference replay failed')
        origin=dict(kind='initial_random_free',lane=lane,initial_domain_sha256=snap.initial_domain_sha256) if lane<INITIAL_LANES else asdict(snap.records[lane-INITIAL_LANES])
        return FreeWitness(FREE_DOMAIN,inputs,state,old,new,lane,'PASS',snap.input_sha256,snap.version,snap.domain_sha256,canonical(origin),(root,tuple(recipe),out))
