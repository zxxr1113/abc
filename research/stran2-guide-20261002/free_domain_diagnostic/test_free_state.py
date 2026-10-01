import copy
from dataclasses import FrozenInstanceError
import json
from pathlib import Path
import tempfile
import unittest
from free_state import (FreeConfig,FreeDomainState,FrozenOriginalAig,domain_projection,
                        INITIAL_LANES,MAX_ADDED_WORLDS)

HERE=Path(__file__).resolve().parent

def graph():return FrozenOriginalAig('1'*64,9,1,((2,20),),(1,),(22,))
def state(enabled=True,cap=256):return FreeDomainState(graph(),[0]*12,(1<<256)-1,FreeConfig(enabled,cap))
def model(world,index):
    bits=[(world>>i)&1 for i in range(10)]
    return dict(domain='unrestricted_one_step_image',reachable_teacher=False,replay='PASS',
        previous_inputs=bits[:9],previous_state=bits[9:],current_inputs=[1]+[0]*8,successor_state=[1],root_value=1,recipe_value=0,
        provenance=dict(input_sha256='1'*64,source_provenance_sha256='2'*64,models_sha256='3'*64,
            source_order=[0,index,index],source_query=index,model_index=index,source_chunk_index=0,source_candidate_index=index,candidate_id=[11,[],0],
            receipt=dict(cnf_sha256='4'*64,queries_sha256='5'*64,results_sha256='6'*64,solver_sha256='7'*64,
                         assumptions=[23],row=index,result='SAT')))

class StateTests(unittest.TestCase):
    def test_disabled_default_is_complete_noop(self):
        s=FreeDomainState(graph(),[0]*12,(1<<256)-1);before=s.snapshot()
        self.assertFalse(s.config.enabled);self.assertEqual(s.config.max_added_worlds,256)
        r=s.append_verified_models(object())
        self.assertEqual(r.status,'DISABLED');self.assertIs(s.snapshot(),before)
        self.assertEqual(r.before_domain_sha256,r.after_domain_sha256)

    def test_config_bounds_and_boolean_types(self):
        for args in [(1,256),(True,257),(True,-1),(True,True)]:
            with self.assertRaises(ValueError):FreeConfig(*args)
        self.assertEqual(state(cap=0).append_verified_models([model(1,1)]).added,0)

    def test_initial_caller_mutation_is_detached(self):
        values=[0]*12;s=FreeDomainState(graph(),values,(1<<256)-1,FreeConfig(True));values[1]=1
        self.assertEqual(s.snapshot().signatures[1],0)

    def test_initial_signatures_are_independently_replayed(self):
        for signatures,mask in [([0]*11,(1<<256)-1),([0]*11+[1],(1<<256)-1),([0]*12,255)]:
            with self.assertRaises(ValueError):FreeDomainState(graph(),signatures,mask)

    def test_original_graph_is_frozen_and_copied(self):
        gates=[[2,20]];g=FrozenOriginalAig('1'*64,9,1,gates,[1],[22]);gates[0][0]=0
        self.assertEqual(g.gates,((2,20),))
        with self.assertRaises(FrozenInstanceError):g.ni=2
        with self.assertRaises(ValueError):FrozenOriginalAig('1'*64,9,1,((22,0),),(1,),(22,))

    def test_file_loader_binds_exact_input(self):
        with tempfile.TemporaryDirectory(dir=HERE) as tmp:
            p=Path(tmp)/'a.aig';p.write_bytes(b'aig 11 9 1 1 1\n1\n22\n'+bytes([2,18]))
            g=FrozenOriginalAig.from_file(p);self.assertEqual(g.gates,((20,2),))
            with self.assertRaises(ValueError):FrozenOriginalAig.from_file(p,'0'*64)

    def test_wrong_domain_and_frame_reject_atomically(self):
        for change in [dict(domain='reset_zero'),dict(reachable_teacher=True),dict(replay='NOT_REPLAYED'),dict(free_pi_field='current_inputs')]:
            s=state();before=s.snapshot();bad=model(2,2);bad.update(change)
            with self.assertRaises(ValueError):s.append_verified_models([model(1,1),bad])
            self.assertIs(s.snapshot(),before)

    def test_malformed_later_row_rejects_entire_batch(self):
        for key,value in [('previous_inputs',[1]*8),('previous_inputs',[True]+[0]*8),('previous_state',[2]),('current_inputs',[1]*8),('successor_state',[False])]:
            s=state();before=s.snapshot();bad=model(2,2);bad[key]=value
            with self.assertRaises(ValueError):s.append_verified_models([model(1,1),bad])
            self.assertIs(s.snapshot(),before)

    def test_transition_and_image_miter_replayed(self):
        for key,value in [('successor_state',[0]),('current_inputs',[0]*9),('root_value',0),('recipe_value',1)]:
            s=state();before=s.snapshot();bad=model(1,1);bad[key]=value
            with self.assertRaises(ValueError):s.append_verified_models([bad])
            self.assertIs(s.snapshot(),before)

    def test_receipt_input_query_and_candidate_bindings(self):
        changes=[lambda p:p.update(input_sha256='0'*64),lambda p:p.update(models_sha256='bad'),
                 lambda p:p['receipt'].update(row=4),lambda p:p['receipt'].update(result='UNKNOWN'),
                 lambda p:p['receipt'].pop('cnf_sha256'),lambda p:p.update(candidate_id=[11,[22,2],-2]),lambda p:p.update(model_index=99),
                 lambda p:p.update(source_candidate_index=99),lambda p:p.update(source_chunk_index=99)]
        for change in changes:
            s=state();bad=model(1,1);change(bad['provenance']);before=s.snapshot()
            with self.assertRaises(ValueError):s.append_verified_models([bad])
            self.assertIs(s.snapshot(),before)

    def test_predecessor_not_current_or_successor_world(self):
        s=state();m=model(2,1);s.append_verified_models([m]);r=s.snapshot().records[0]
        self.assertEqual(r.inputs,tuple(m['previous_inputs']));self.assertNotEqual(r.inputs,tuple(m['current_inputs']))
        self.assertEqual(r.state,(0,));self.assertNotEqual(r.state,tuple(m['successor_state']))
        self.assertEqual(r.sampled_pi_field,'previous_inputs');self.assertEqual(r.source_query,1);self.assertEqual(r.source_model_index,1)
        self.assertEqual(json.loads(r.provenance_json),m['provenance'])
        m['previous_inputs'][0]=1;m['previous_state'][0]=1
        self.assertEqual(r.inputs[0],0);self.assertEqual(r.state,(0,))
        m['provenance']['receipt']['assumptions'][0]=999
        self.assertEqual(json.loads(r.provenance_json)['receipt']['assumptions'],[23])

    def test_dedup_initial_and_appended_before_cap(self):
        s=state(cap=2);r=s.append_verified_models([model(0,0),model(1,1),model(1,2),model(2,3),model(3,4)])
        self.assertEqual(r.added,2)
        self.assertEqual([x.action for x in r.decisions],['EXACT_FREE_WORLD_DUPLICATE','APPEND_PREDECESSOR_FREE_WORLD','EXACT_FREE_WORLD_DUPLICATE','APPEND_PREDECESSOR_FREE_WORLD','GLOBAL_FREE_CAP_REACHED'])
        self.assertEqual([x.source_model_index for x in s.snapshot().records],[1,3])
        self.assertEqual([x.lane for x in s.snapshot().records],[256,257])

    def test_global256_cap_across_calls(self):
        s=state();s.append_verified_models([model(i,i) for i in range(1,131)])
        r=s.append_verified_models([model(i,i) for i in range(131,261)])
        snap=s.snapshot();self.assertEqual(len(snap.records),MAX_ADDED_WORLDS);self.assertEqual(snap.lanes,512)
        self.assertEqual(r.added,126);self.assertEqual(sum(d.action=='GLOBAL_FREE_CAP_REACHED' for d in r.decisions),4)
        self.assertEqual(s.append_verified_models([model(300,300)]).added,0)
        self.assertEqual(len(s.snapshot().records),256)

    def test_invalid_row_beyond_cap_still_rejects_atomically(self):
        s=state(cap=1);before=s.snapshot();bad=model(2,2);bad['previous_state']=[9]
        with self.assertRaises(ValueError):s.append_verified_models([model(1,1),bad])
        self.assertIs(s.snapshot(),before)

    def test_strict_global_source_order(self):
        s=state();before=s.snapshot()
        with self.assertRaises(ValueError):s.append_verified_models([model(1,2),model(2,1)])
        self.assertIs(s.snapshot(),before);s.append_verified_models([model(1,3)]);after=s.snapshot()
        with self.assertRaises(ValueError):s.append_verified_models([model(2,3)])
        self.assertIs(s.snapshot(),after)

    def test_witness_lanes_and_provenance_never_wrap(self):
        s=state();initial=s.snapshot();s.append_verified_models([model(1,1)]);first=s.snapshot()
        w=s.witness(11,[],2);self.assertEqual(w.lane,256);self.assertEqual(w.inputs,(1,)+(0,)*8);self.assertEqual(w.state,(0,))
        s.append_verified_models([model(513,2)]);second=s.snapshot()
        self.assertEqual(s.witness(11,[],2,lane=256,snapshot=first),w)
        self.assertEqual(s.witness(11,[],2,lane=256).inputs,w.inputs)
        self.assertEqual([x&initial.mask for x in second.signatures],list(initial.signatures))
        self.assertEqual([x&first.mask for x in second.signatures],list(first.signatures))
        self.assertEqual(s.witness(11,[],0).lane,257)
        self.assertEqual(json.loads(w.origin_json)['source_model_index'],1)
        self.assertEqual(w.candidate_id,(11,(),2))
        with self.assertRaises(ValueError):s.witness(11,[],2,lane=0)

    def test_dual_domain_projection_cache_rule(self):
        s=state();seq=[0]*12;before=domain_projection(11,[1],seq,1,0,s.snapshot())
        s.append_verified_models([model(2,1)]);irrelevant=domain_projection(11,[1],seq,1,0,s.snapshot())
        self.assertTrue(irrelevant.can_reuse_search(before))
        s.append_verified_models([model(1,2)]);changed=domain_projection(11,[1],seq,1,0,s.snapshot())
        self.assertFalse(changed.can_reuse_search(irrelevant))
        seq[11]=1;seqchanged=domain_projection(11,[1],seq,1,1,s.snapshot())
        self.assertFalse(seqchanged.can_reuse_search(changed))
        differentpool=domain_projection(11,[2],seq,1,1,s.snapshot())
        with self.assertRaises(ValueError):differentpool.can_reuse_search(seqchanged)

    def test_projection_rejects_graph_and_ordered_pool_changes(self):
        s=state();seq=[0]*12;a=domain_projection(11,[1,2],seq,1,0,s.snapshot())
        b=domain_projection(11,[2,1],seq,1,0,s.snapshot())
        with self.assertRaises(ValueError):b.can_reuse_search(a)
        different=FrozenOriginalAig('8'*64,9,1,((2,20),),(1,),(22,))
        other=FreeDomainState(different,[0]*12,(1<<256)-1)
        c=domain_projection(11,[1,2],seq,1,0,other.snapshot())
        with self.assertRaises(ValueError):c.can_reuse_search(a)

    def test_oversized_batch_rejects_atomically(self):
        s=state();before=s.snapshot()
        with self.assertRaises(ValueError):s.append_verified_models([model(i,i) for i in range(257)])
        self.assertIs(s.snapshot(),before)

    def test_external_seq_and_qualified_identities_untouched(self):
        s=state();seq=[0]*12;version=7;qualified=[('old',i) for i in range(49)];copyseq=list(seq);copyq=list(qualified)
        projection=domain_projection(11,[1],seq,1,version,s.snapshot());s.append_verified_models([model(1,1)])
        self.assertEqual(seq,copyseq);self.assertEqual(qualified,copyq);self.assertEqual(version,7)
        self.assertEqual(projection.sequence_version,7)
        qualified.extend(('new',i) for i in range(3));self.assertEqual(len(qualified),52)

    def test_snapshot_serialization_is_detached(self):
        s=state();s.append_verified_models([model(1,1)]);snap=s.snapshot();export=snap.to_dict()
        json.dumps(export);export['signature_hex'][1]='0x0';export['records'][0]['lane']=0
        self.assertEqual(s.snapshot(),snap);self.assertEqual(snap.records[0].lane,256)
        with self.assertRaises(FrozenInstanceError):snap.mask=1


import os
@unittest.skipUnless(os.environ.get('STRAN2_FREE_DIAGNOSTIC_RUN'),'set STRAN2_FREE_DIAGNOSTIC_RUN for frozen-model state replay')
class SavedModelStateTests(unittest.TestCase):
    def test_all_four_saved_predecessor_domains_match_exactly(self):
        from free_state import digest,file_sha
        run=Path(os.environ['STRAN2_FREE_DIAGNOSTIC_RUN']);plan=json.loads((run/'plan.json').read_text());source=Path(plan['source'])
        for name in plan['protocol']['cases']:
            with self.subTest(case=name):
                freeze=json.loads((run/name/'frozen_inputs.json').read_text());folder=source/name/'models'
                saved=json.loads((folder/'replayed_models.json').read_text());prov=json.loads((folder/'provenance.json').read_text());report=json.loads((folder/'report.json').read_text())
                self.assertEqual(file_sha(folder/'models.jsonl'),report['models_sha256'])
                self.assertEqual(file_sha(folder/'provenance.json'),saved[0]['source_provenance_sha256'] if saved else file_sha(folder/'provenance.json'))
                g=FrozenOriginalAig.from_file(freeze['input'],freeze['input_sha256']);s=FreeDomainState(g,freeze['initial_free_signatures'],freeze['initial_free_mask'],FreeConfig(True))
                rows=[]
                for index,original in enumerate(saved):
                    row=copy.deepcopy(original);query=row['query'];row['provenance']=dict(
                        input_sha256=freeze['input_sha256'],source_provenance_sha256=file_sha(folder/'provenance.json'),models_sha256=report['models_sha256'],
                        source_order=[0,query,index],source_query=query,model_index=index,source_chunk_index=0,source_candidate_index=query,candidate_id=row['candidate_id'],
                        receipt=dict(cnf_sha256=prov['cnf_sha256'],queries_sha256=prov['queries_sha256'],results_sha256=report['results_sha256'],
                                     solver_sha256=prov['helper_sha256'],assumptions=[prov['query_sources'][query]['miter']],row=query,result='SAT'))
                    rows.append(row)
                result=s.append_verified_models(rows);snap=s.snapshot()
                self.assertEqual(result.added,freeze['arms']['B']['added'])
                self.assertEqual(digest(dict(free=snap.signatures,mask=snap.mask)),freeze['arms']['B']['free_domain_sha256'])
                expected=freeze['arms']['B']['extra_worlds']
                self.assertEqual([(r.inputs,r.state,r.source_model_index) for r in snap.records],[(tuple(r['inputs']),tuple(r['state']),r['source_model_index']) for r in expected])

if __name__=='__main__':unittest.main()

