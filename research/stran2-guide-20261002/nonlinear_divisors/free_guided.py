"""Opt-in bridge from authenticated inline models to append-only free worlds.

No source model solve is added. The existing full/cone validator runs first;
this bridge rebinds exact receipt/model bytes before predecessor admission.
"""
from __future__ import annotations
from dataclasses import asdict
import copy
import json
from pathlib import Path
import sys
import prototype as p

STATE_DIRECTORY = Path(__file__).resolve().parents[1] / 'free_domain_diagnostic'
sys.path.insert(0, str(STATE_DIRECTORY))
import free_state as fs
p.require(Path(fs.__file__).resolve() == STATE_DIRECTORY / 'free_state.py', 'wrong free-state module')
p.require(Path(sys.modules[fs.Aig.__module__].__file__).resolve() == STATE_DIRECTORY / 'independent.py',
          'wrong independent free-state decoder')
RUNTIME = ['nonlinear_divisors/free_guided.py', 'free_domain_diagnostic/free_state.py',
           'free_domain_diagnostic/independent.py']
CONE_VALIDATOR = 'exact_assumption_cone_on_immutable_verified_Tseitin_DAG'


def validate_mode(job, config, chunk_roots):
    if not job.get('predecessor_free'):
        return
    p.require(job.get('inline_image_models') is True and not job.get('image_model_solver'),
              'predecessor-free requires original inline image models; helper mode is unsupported')
    p.require(config.lanes == 256 and 0 < chunk_roots * config.candidates_per_root <= 256,
              'predecessor-free requires256 initial lanes and at most256 candidates per chunk')


def safe_chunk(name):
    p.require(type(name) is str and name.startswith('chunk_') and name[6:].isdigit(), 'invalid free source chunk')
    return int(name[6:])


class PredecessorFreeDomain:
    def __init__(self, a, graph, base, step, free, mask, job, config, deadline):
        validate_mode(job, config, job['chunk_roots'])
        self.a, self.graph, self.base, self.step = a, graph, base, step
        self.job, self.deadline = job, deadline
        self.out = Path(job['out'])
        self.directory = self.out / 'free_domains'
        self.directory.mkdir(exist_ok=False)
        deadline.remaining()
        original = fs.FrozenOriginalAig.from_file(job['case']['input'], job['case']['input_sha256'])
        self.state = fs.FreeDomainState(original, free, mask, fs.FreeConfig(enabled=True))
        deadline.remaining()
        self.initial_ci = [hex(v) for v in free[1:1+a.ni+a.nl]]
        self.manifests = {}
        self.persist()

    def persist(self):
        self.deadline.remaining()
        snap = self.state.snapshot()
        name = f'version_{snap.version:05d}.json'
        path = self.directory / name
        payload = dict(schema=1, domain=fs.FREE_DOMAIN, input_sha256=snap.input_sha256,
            free_version=snap.version, free_mask=hex(snap.mask), free_signature_bits=snap.lanes,
            free_domain_sha256=snap.domain_sha256, initial_domain_sha256=snap.initial_domain_sha256,
            initial_ci_signatures=self.initial_ci, initial_lanes=256, global_added_cap=256,
            sampled_pi_field='previous_inputs', records=[asdict(r) for r in snap.records])
        if snap.version in self.manifests:
            old = self.manifests[snap.version]
            p.require(p.sha(path) == old['sha256'] and json.loads(path.read_text()) == json.loads(fs.canonical(payload)),
                      'immutable free-domain manifest changed')
            return old
        p.require(not path.exists(), 'free-domain manifest already exists')
        p.write_json(path, payload)
        self.deadline.remaining()
        bound = dict(file=name, sha256=p.sha(path), free_version=snap.version,
                     free_domain_sha256=snap.domain_sha256, free_signature_bits=snap.lanes)
        self.manifests[snap.version] = bound
        return bound

    def projection(self, row, seq, mask, version):
        return fs.domain_projection(row['root'], row['pool'], seq, mask, version, self.state.snapshot())

    def annotate(self, candidates):
        manifest = self.persist()
        for c in candidates:
            self.deadline.remaining()
            witness = self.state.witness(c['root'], c['recipe'], c['out'], lane=c['witness_lane'])
            c['free_domain'] = dict(schema=1, policy='authenticated_predecessor_PI_RO_only',
                manifest=copy.deepcopy(manifest), witness=witness.to_dict())

    def admit(self, sources, target, report, replayed):
        """Authenticate exact raw projections again before any state mutation."""
        from inline_models import read_model_batch, bound_model, d
        self.deadline.remaining()
        p.require(p.sha(target/'provenance.json') == report['provenance_sha256'] and
                  p.sha(target/'replayed_models.json') == report['replayed_models_sha256'],
                  'inline replay artifact changed before free admission')
        provenance = json.loads((target/'provenance.json').read_text())
        p.require(provenance['mode'] == 'original_ordinary_step_sat' and
                  provenance['additional_solver_queries'] == 0 and report['additional_solver_queries'] == 0,
                  'free admission source was not original inline model')
        if self.job.get('inline_cone_check'):
            p.require(provenance.get('compiled_model_validator') == report.get('compiled_model_validator') == CONE_VALIDATOR,
                      'free admission lost exact cone-validator binding')
        roles, variables = d.projected_pis(self.graph, self.base, self.step, self.a)
        expected = dict(input_sha256=self.job['case']['input_sha256'], source_hashes=self.job['source_hashes'],
                        solver_sha256=self.job['solver_sha256'], roles=roles, variables=variables)
        for key,value in expected.items():
            p.require(provenance[key] == value, 'inline/free provenance mismatch: '+key)
        source_by_id = {d.candidate_id(c):c for c in sources}
        p.require(len(source_by_id) == len(sources), 'duplicate free source candidate identity')
        batches, rows = {}, []
        p.require(len(replayed) == report['models'] == len(provenance['query_sources']), 'free model/source cardinality mismatch')
        for row, origin in zip(replayed, provenance['query_sources']):
            self.deadline.remaining()
            identity = row['candidate_id'][0], tuple(row['candidate_id'][1]), row['candidate_id'][2]
            p.require(identity in source_by_id, 'free source model not in eligible proof set')
            c = source_by_id[identity]; cert = c['anytime_certificate']; receipt = cert['receipts']['step']
            p.require((c['proof']['free'],c['proof']['reset'],c['proof']['step']) == ('SAT','UNSAT','SAT'),
                      'ineligible free source relation')
            p.require(cert['input_sha256'] == expected['input_sha256'] and cert['root'] == c['root'] and
                      cert['recipe'] == c['recipe'] and cert['out'] == c['out'], 'free source certificate differs')
            reference = receipt.get('inline_image_model')
            p.require(reference is not None and receipt == row['source_receipt'] and
                      receipt['assumptions'] == [cert['miter_literals']['step']] and receipt['cnf_sha256'] == cert['cnf_sha256'],
                      'free source exact receipt differs')
            name = cert['chunk']; chunk_index = safe_chunk(name)
            p.require(row['source_chunk'] == origin['chunk'] == name and
                      row['source_proof_candidate_index'] == origin['candidate_index'] == cert['candidate_index'] and
                      origin['reference'] == reference and row['source_provenance_sha256'] == report['provenance_sha256'],
                      'free source candidate/order/provenance mismatch')
            key = name, reference['manifest_file'], reference['manifest_sha256']
            if key not in batches:
                batches[key] = read_model_batch(self.out/'chunks'/name, reference, dict(expected,cnf_sha256=cert['cnf_sha256']))
            batch = batches[key]; model = bound_model(receipt, reference, batch)
            assignment = dict(zip(variables,model['values']))
            for field in ('previous_inputs','previous_state','current_inputs'):
                raw = [assignment[lit//2]^(lit&1) for lit in roles[field]]
                p.require(raw == row[field], 'free replay row differs from authenticated raw '+field)
            p.require(row['successor_state'] == self.a.step(row['previous_inputs'],row['previous_state'])[1],
                      'free source successor differs')
            candidate_index=cert['candidate_index']; model_index=reference['model_row']
            normalized=copy.deepcopy(row)
            normalized['provenance']=dict(input_sha256=expected['input_sha256'],
                source_provenance_sha256=report['provenance_sha256'], models_sha256=batch[0]['artifacts']['models']['sha256'],
                source_order=[chunk_index,candidate_index,model_index], source_query=receipt['row'], model_index=model_index,
                source_chunk_index=chunk_index,source_candidate_index=candidate_index,candidate_id=row['candidate_id'],
                source_chunk=name, model_manifest=copy.deepcopy(reference),
                receipt=dict(receipt,solver_sha256=expected['solver_sha256']))
            rows.append(normalized)
        self.deadline.remaining()
        result=self.state.append_verified_models(rows)
        # A late/failed admission can never reach a candidate proof/checkpoint.
        self.deadline.remaining()
        if result.added:
            self.persist()
        return asdict(result)

    def report(self):
        snap=self.state.snapshot()
        return dict(enabled=True, free_version=snap.version, free_signature_bits=snap.lanes,
                    free_domain_sha256=snap.domain_sha256, added_free_worlds=len(snap.records),
                    global_added_cap=256, sampled_pi_field='previous_inputs', proof_domain_unchanged=True)


def verify_witness_annotation(a, candidate, ordinary_witness, case_out, input_hash):
    """Bind a preserved full witness to its immutable discovery free snapshot."""
    annotation=candidate['free_domain'];bound=annotation['manifest'];w=annotation['witness']
    p.require(annotation['schema']==1 and annotation['policy']=='authenticated_predecessor_PI_RO_only', 'wrong free witness policy')
    name=bound['file'];p.require(type(name) is str and name.startswith('version_') and name.endswith('.json') and
        name[8:-5].isdigit() and Path(name).name==name, 'invalid free manifest path')
    path=Path(case_out)/'free_domains'/name
    p.require(p.sha(path)==bound['sha256'], 'free witness manifest hash differs')
    manifest=json.loads(path.read_text())
    p.require(manifest['input_sha256']==w['input_sha256']==input_hash and manifest['domain']=='unrestricted_free_PI_RO' and
              manifest['free_version']==w['free_version']==bound['free_version'] and
              manifest['free_domain_sha256']==w['free_domain_sha256']==bound['free_domain_sha256'] and
              manifest['free_signature_bits']==bound['free_signature_bits'], 'free witness snapshot binding differs')
    p.require(w['candidate_id']==[candidate['root'],candidate['recipe'],candidate['out']] or
              w['candidate_id']==(candidate['root'],tuple(candidate['recipe']),candidate['out']), 'free witness candidate binding differs')
    p.require(w['kind']=='unrestricted_free_PI_RO' and w['replay']=='PASS', 'unreplayed/wrong free witness')
    for key in ('inputs','state'):
        p.require(list(w[key])==ordinary_witness[key], 'free witness assignment changed before proof')
    for key in ('root','replacement','lane'):
        p.require(w[key]==ordinary_witness[key], 'free witness value/lane changed before proof')
    lane=w['lane'];p.require(type(lane) is int and 0<=lane<manifest['free_signature_bits']<=512, 'invalid free witness lane')
    p.require(int(manifest['free_mask'],16)==(1<<manifest['free_signature_bits'])-1 and manifest['initial_lanes']==256 and
              manifest['global_added_cap']==256 and manifest['sampled_pi_field']=='previous_inputs', 'free manifest bounds/frame differ')
    if lane<256:
        assignment=[(int(v,16)>>lane)&1 for v in manifest['initial_ci_signatures']]
        origin=dict(kind='initial_random_free',lane=lane,initial_domain_sha256=manifest['initial_domain_sha256'])
    else:
        records=manifest['records'];p.require(len(records)==manifest['free_signature_bits']-256, 'free lane records incomplete')
        origin=records[lane-256];p.require(origin['lane']==lane and origin['sampled_pi_field']=='previous_inputs' and
                                        origin['domain']=='unrestricted_free_PI_RO','free lane provenance/frame differs')
        assignment=origin['inputs']+origin['state']
    p.require(assignment==ordinary_witness['inputs']+ordinary_witness['state'] and
              fs.digest(origin)==fs.digest(json.loads(w['origin_json'])), 'free witness lane origin differs')
    p.require(len(ordinary_witness['inputs'])==a.ni and len(ordinary_witness['state'])==a.nl and
              all(type(x) is int and x in (0,1) for x in assignment),'incomplete/non-Boolean free witness')
    values=a.step(ordinary_witness['inputs'],ordinary_witness['state'])[2]
    p.require(values[candidate['root']]==ordinary_witness['root'] and
              p.recipe_eval(candidate['recipe'],candidate['out'],values)==ordinary_witness['replacement'] and
              ordinary_witness['root']!=ordinary_witness['replacement'],'independent original witness replay differs')
    return fs.digest(annotation)


def reconstruct_free_manifest(a, case_out, bound, input_hash, expected_initial_free=None):
    """Extra-cost auditor reconstruction of EVERY lane, never a synthetic slot."""
    name=bound['file']
    p.require(type(name) is str and name.startswith('version_') and name.endswith('.json') and
              name[8:-5].isdigit() and Path(name).name==name,'invalid audit free manifest path')
    path=Path(case_out)/'free_domains'/name
    p.require(p.sha(path)==bound['sha256'],'audit free manifest hash differs')
    manifest=json.loads(path.read_text())
    p.require(manifest['schema']==1 and manifest['domain']==fs.FREE_DOMAIN and manifest['input_sha256']==input_hash and
              manifest['free_version']==bound['free_version'] and manifest['free_domain_sha256']==bound['free_domain_sha256'] and
              manifest['free_signature_bits']==bound['free_signature_bits'] and manifest['initial_lanes']==256 and
              manifest['global_added_cap']==256 and manifest['sampled_pi_field']=='previous_inputs','audit free manifest binding differs')
    initial_mask=(1<<256)-1
    ci=[int(v,16) for v in manifest['initial_ci_signatures']]
    p.require(len(ci)==a.ni+a.nl and all(0<=v<=initial_mask for v in ci),'invalid initial free CI signatures')
    values=[0]+ci
    for x,y in a.gates:
        values.append((values[x//2]^(initial_mask if x&1 else 0))&(values[y//2]^(initial_mask if y&1 else 0)))
    p.require(fs.digest(dict(input_sha256=input_hash,signatures=values,mask=initial_mask))==manifest['initial_domain_sha256'],
              'initial full free-domain hash differs')
    if expected_initial_free is not None:
        p.require(values==list(expected_initial_free),'initial free domain differs from frozen seed/config')
    seen={tuple((values[n]>>lane)&1 for n in range(1,a.ni+a.nl+1)) for lane in range(256)}
    records=manifest['records'];p.require(len(records)<=256 and manifest['free_signature_bits']==256+len(records),'missing/excess free records')
    previous=None
    for i,record in enumerate(records):
        lane=256+i
        p.require(record['lane']==lane and record['domain']==fs.FREE_DOMAIN and record['sampled_pi_field']=='previous_inputs',
                  'free record lane/domain/frame differs')
        inputs=fs.bits(record['inputs'],a.ni,'audit predecessor PI');state=fs.bits(record['state'],a.nl,'audit predecessor RO')
        order=tuple(record['source_order']);origin=json.loads(record['provenance_json'])
        p.require(len(order)==3 and all(type(x) is int and x>=0 for x in order) and (previous is None or order>previous),
                  'free source order differs')
        p.require(order==tuple(origin['source_order'])==(origin['source_chunk_index'],origin['source_candidate_index'],origin['model_index']) and
                  record['source_query']==origin['source_query']==origin['receipt']['row'] and record['source_model_index']==origin['model_index'] and
                  record['source_candidate_id']==origin['candidate_id'] and origin['input_sha256']==input_hash,
                  'free source record/provenance differs')
        key=inputs+state;p.require(key not in seen,'duplicate free world in saved domain');seen.add(key);previous=order
        row=a.step(list(inputs),list(state))[2]
        for node,bit in enumerate(row):values[node]|=bit<<lane
    mask=(1<<manifest['free_signature_bits'])-1
    p.require(int(manifest['free_mask'],16)==mask and fs.digest(dict(input_sha256=input_hash,signatures=values,mask=mask))==manifest['free_domain_sha256'],
              'reconstructed full free-domain hash differs')
    return values,manifest
