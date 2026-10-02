"""Exact chosen-set reconstruction, DSEC-bound emission and Direct dominance."""
from __future__ import annotations
import copy
from pathlib import Path
import time
from support import *

class Products:
    def __init__(self,p,product,a,ia,global_module,inputpath,abc,out,deadline,bindings):
        self.p,self.product,self.a,self.ia,self.global_module=p,product,a,ia,global_module
        self.inputpath,self.abc,self.out=Path(inputpath),Path(abc),Path(out)
        self.deadline,self.bindings=deadline,bindings
        self.cache={};self.results={};self.emitted=Bindings();self.inputhash=sha(inputpath);self.abchash=sha(abc)
    def emit(self,label,selected):
        self.deadline.remaining();directory=self.out/label;directory.mkdir(parents=True)
        self.bindings.check(self.deadline)
        graph=self.product.rebuild(self.a,selected,self.deadline)
        h=self.product.write_aig(directory/'product.aig',graph)
        write_new(directory/'selection.json',dict(selected=selected,realization=graph['realization']))
        self.emitted.add(directory/'product.aig',h);self.emitted.add(directory/'selection.json')
        self.emitted.check(self.deadline)
        replay=replay_independent(self.ia,selected,directory/'product.aig',self.global_module,self.inputpath)
        key=(self.inputhash,h,self.abchash)
        if key in self.cache:
            cert=copy.deepcopy(self.cache[key]);cert.update(reused_exact_graph_dsec=True,charged_new_wall_s=0.0)
        else:
            self.bindings.check(self.deadline)
            cert=self.product.dsec(self.abc,self.inputpath,directory/'product.aig',directory,min(120,self.deadline.remaining()),'dsec')
            self.bindings.check(self.deadline)
            cert.update(reused_exact_graph_dsec=False,charged_new_wall_s=cert['wall_s'],
                log_path=str((directory/'dsec.log').resolve()),input_sha256=self.inputhash,
                product_sha256=h,abc_sha256=self.abchash)
            write_new(directory/'dsec_receipt.json',cert)
            self.emitted.add(directory/'dsec.log',cert['log_sha256']);self.emitted.add(directory/'dsec_receipt.json')
            require(cert['status']=='PASS','independent DSEC failed/unknown/timeout')
            self.cache[key]=copy.deepcopy(cert)
        self.emitted.check(self.deadline)
        require(cert['input_sha256']==sha(self.inputpath) and cert['product_sha256']==h==sha(directory/'product.aig') and
                cert['abc_sha256']==sha(self.abc) and sha(cert['log_path'])==cert['log_sha256'],'DSEC binding changed')
        result=dict(and_count=len(graph['gates']),product_sha256=h,selected=len(selected),dsec=cert,
                    independent_product_replay=replay)
        write_new(directory/'result.json',result);self.emitted.add(directory/'result.json');self.results[label]=result
        self.deadline.remaining();return result,graph
    def cost_summary(self):
        return dict(fresh_dsec_runs=len(self.cache),fresh_dsec_wall_s=sum(x['wall_s'] for x in self.cache.values()),
                    graph_products=len(self.results),reused_dsec_products=len(self.results)-len(self.cache))

def check_selection(p,s,selected):
    """Independent explicit check of the conservative selector's conflicts."""
    roots=set();removed=set();kept=set()
    for c in selected:
        if c['root'] in roots:return False,'same_root'
        cost=s.cost(c['root'],c['recipe'],c['out']);deleting=set(cost['removable_nodes'])
        keeping=s.tfi(p.external_nodes(c['recipe'],c['out']))
        if deleting&removed:return False,'overlapping_deletion'
        if deleting&kept or keeping&removed:return False,'divisor_dependency_conflict'
        roots.add(c['root']);removed|=deleting;kept|=keeping
    return True,None

def run_selection_family(p,s,product,emitter,label,selected,classifications,newids):
    compatible,reason=check_selection(p,s,selected);require(compatible,'actual selection conflicts: '+str(reason))
    full,graph=emitter.emit(label+'/full',selected)
    sets,genuine=removal_sets(selected,graph['realization'],classifications,newids)
    rows={'full':full}
    for name in ('without_new_identities','without_all_genuine','without_new_genuine'):
        # Deliberately no call to select: exact subsets of this actual selection.
        rows[name],_=emitter.emit(label+'/'+name,sets[name])
    metadata=dict(selected=selected,genuine_ids=[[i[0],list(i[1]),i[2]] for i in sorted(genuine)],
        same_selected_subsets=sets,products=rows,
        new_identity_same_set_marginal=rows['without_new_identities']['and_count']-full['and_count'],
        all_genuine_build_same_set_marginal=rows['without_all_genuine']['and_count']-full['and_count'],
        new_genuine_build_same_set_marginal=rows['without_new_genuine']['and_count']-full['and_count'])
    write_new(emitter.out/label/'attribution.json',metadata);return metadata

def dominance(p,s,product,emitter,label,selected,directs,full_result):
    """Fixed-other-choice exact counterfactuals; DSEC the best cheaper alternative."""
    byroot={}
    for c in directs:byroot.setdefault(c['root'],[]).append(c)
    results=[]
    for chosen in selected:
        if not chosen['recipe']:continue
        emitter.deadline.remaining();alternatives=[];realizations={}
        for d in byroot.get(chosen['root'],[]):
            counterfactual=[d if cid(c)==cid(chosen) else c for c in selected]
            graph=product.rebuild(emitter.a,counterfactual,emitter.deadline)
            compatible,reason=check_selection(p,s,counterfactual)
            count=len(graph['gates']);key=(count,d['out'])
            alternatives.append(dict(literal=d['out'],and_count=count,
                improvement_over_fixed_other_choices=full_result['and_count']-count,
                selector_compatible=compatible,selector_conflict=reason,
                source_direct_identity=[d['root'],d['recipe'],d['out']],dsec='NOT_RUN'))
            realizations[key]=counterfactual
        alternatives.sort(key=lambda x:(x['and_count'],x['literal']))
        best=alternatives[0] if alternatives else None;validated=None
        if best and best['and_count']<full_result['and_count']:
            key=(best['and_count'],best['literal'])
            validated,_=emitter.emit(label+f'/root_{chosen["root"]}_best_direct',realizations[key])
            require(validated['and_count']==best['and_count'],'best Direct replay AND differs')
            best['dsec']='PASS'
        results.append(dict(root=chosen['root'],build_identity=[chosen['root'],chosen['recipe'],chosen['out']],
            full_selected_and=full_result['and_count'],alternatives=alternatives,
            best_cheaper_direct_validated=validated,
            interpretation='Other selected choices are unchanged. Non-best alternatives are structure-only diagnostics, not DSEC-validated products'))
    write_new(emitter.out/(label.replace('/','_')+'.json'),results);return results
