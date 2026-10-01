#!/usr/bin/env python3
"""Independent adversarial review; no mutations of any frozen evidence.

Set STRAN2_FROZEN_PACKAGE to the saved anytime source directory. The binary
AIGER decoder, original-transition simulator, and recipe evaluator below do not
use the implementation's corresponding functions.
"""
from __future__ import annotations

import importlib.util
import itertools
import copy
import csv
import hashlib
from collections import Counter
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PACKAGE = Path(os.environ.get("STRAN2_FROZEN_PACKAGE", str(HERE.parent)))
sys.path.insert(0, str(PACKAGE / "nonlinear_divisors"))
import prototype as runtime


def decode_aiger(path):
    """Independent dense binary decoder, intentionally not runtime.Aiger."""
    with Path(path).open("rb") as stream:
        header = stream.readline().split()
        assert header[0] == b"aig" and len(header) == 6
        m, ni, nl, no, na = (int(x) for x in header[1:])
        assert min(m, ni, nl, no, na) >= 0 and m == ni + nl + na
        latches = []
        for _ in range(nl):
            row = [int(x) for x in stream.readline().split()]
            assert len(row) in (1, 2) and (len(row) == 1 or row[1] == 0)
            latches.append(row[0])
        outputs = [int(stream.readline()) for _ in range(no)]
        def delta():
            answer = 0
            for shift in range(0, 64, 7):
                ch = stream.read(1)
                assert len(ch) == 1
                byte = ord(ch)
                answer += (byte % 128) * (2 ** shift)
                if byte < 128:
                    return answer
            raise AssertionError("invalid variable-length delta")
        gates = []
        for node in range(ni + nl + 1, m + 1):
            first = 2 * node - delta()
            second = first - delta()
            assert 0 <= second <= first < 2 * node
            gates.append((first, second))
    assert all(0 <= literal < 2 * (m + 1) for literal in latches + outputs)
    return SimpleNamespace(m=m, ni=ni, nl=nl, no=no, na=na, gates=gates,
                           latches=latches, outputs=outputs, initial=[0] * nl)


def fixture(ni, nl, gates, latches, outputs):
    return SimpleNamespace(ni=ni, nl=nl, no=len(outputs), m=ni + nl + len(gates),
                           na=len(gates), gates=gates, latches=latches,
                           outputs=outputs, initial=[0] * nl)


def original_eval(a, pi, state):
    assert len(pi) == a.ni and len(state) == a.nl
    assert all(type(x) is int and x in (0, 1) for x in list(pi) + list(state))
    v = [0] + list(pi) + list(state)
    def get(literal):
        return (1 - v[literal >> 1]) if literal % 2 else v[literal >> 1]
    for x, y in a.gates:
        v.append(int(get(x) and get(y)))
    return v, [get(x) for x in a.latches], [get(x) for x in a.outputs]


def original_recipe(candidate, values):
    constructed = []
    def get(code):
        if code >= 0:
            bit = values[code // 2]
            return 1 - bit if code % 2 else bit
        assert code <= -2
        index, phase = divmod(-code - 2, 2)
        assert index < len(constructed)
        return 1 - constructed[index] if phase else constructed[index]
    recipe = candidate["recipe"]
    assert len(recipe) % 2 == 0
    for i in range(0, len(recipe), 2):
        constructed.append(int(get(recipe[i]) and get(recipe[i + 1])))
    return get(candidate["out"])


def compiled_eval(graph, assignment):
    values = [0]
    for index, gate in enumerate(graph.gates[1:], 1):
        if gate is None:
            values.append(assignment[index])
        else:
            a, b = gate
            values.append((values[a // 2] ^ (a % 2)) & (values[b // 2] ^ (b % 2)))
    return values


def mapped_values(values, mapping):
    return [values[x // 2] ^ (x % 2) for x in mapping]


class IndependentCompilerTests(unittest.TestCase):
    def check(self, a):
        graph, base, image, reset = runtime.compile_graph(a)
        variable_ids = [i for i, gate in enumerate(graph.gates) if i and gate is None]
        self.assertEqual(len(variable_ids), 2 * a.ni + a.nl)
        for bits in itertools.product((0, 1), repeat=len(variable_ids)):
            assignment = dict(zip(variable_ids, bits))
            values = compiled_eval(graph, assignment)
            pi = [assignment[x // 2] for x in base[1:1 + a.ni]]
            pred = [assignment[x // 2] for x in base[1 + a.ni:1 + a.ni + a.nl]]
            current_pi = [assignment[x // 2] for x in image[1:1 + a.ni]]
            b, successor, _ = original_eval(a, pi, pred)
            im, _, _ = original_eval(a, current_pi, successor)
            re, _, _ = original_eval(a, current_pi, [0] * a.nl)
            self.assertEqual(mapped_values(values, base), b)
            self.assertEqual(mapped_values(values, image), im)
            self.assertEqual(mapped_values(values, reset), re)
        return graph, base, image, reset

    def test_exhaustive_constant_complement_and_frame_mapping(self):
        self.check(fixture(2, 2, [(3, 6), (5, 8), (10, 13)], [11, 1], [14, 9]))
        self.check(fixture(0, 1, [], [2], [2]))
        self.check(fixture(2, 0, [(2, 4)], [], [6]))
        rng = random.Random(202610011)
        for _ in range(35):
            self.check(fixture(2, 2,
                       [tuple(rng.randrange(2 * node) for _ in range(2)) for node in range(5, 9)],
                       [rng.randrange(18), rng.randrange(18)], [rng.randrange(18)]))

    def test_unreachable_image_model_is_not_reachable(self):
        # q'=q, q(0)=0. A model with q=1 belongs to unrestricted image but
        # cannot be a reset-reachable teacher; it is valid only for this proof class.
        a = fixture(0, 1, [], [2], [2])
        candidate = {"root": 1, "recipe": [], "out": 0}
        values, successor, _ = original_eval(a, [], [1])
        self.assertEqual(successor, [1])
        self.assertNotEqual(values[1], original_recipe(candidate, values))
        state = [0]
        for _ in range(8):
            values, state, _ = original_eval(a, [], state)
            self.assertEqual(values[1], original_recipe(candidate, values))


def load_diagnostic():
    spec = importlib.util.spec_from_file_location("image_cegar_under_review", HERE / "diagnostic.py")
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


diagnostic = load_diagnostic()


def attach_step(a):
    def step(pi, state):
        values, successor, outputs = original_eval(a, pi, state)
        return outputs, successor, values
    a.step = step
    return a


class ModelReplayTests(unittest.TestCase):
    def setup_image(self):
        a = attach_step(fixture(1, 2, [(4, 6)], [2, 1], [8]))
        c = dict(root=4, recipe=[2, 6], out=-2)
        graph, base, image, reset = runtime.compile_graph(a)
        roles, variables = diagnostic.projected_pis(graph, base, image, a)
        miter = graph.xor(image[4], runtime.graph_recipe(graph, image, c["recipe"], c["out"]))
        # u=1, arbitrary predecessor q=(0,0), x=0; successor q=(1,1).
        assignment = dict(zip([x // 2 for x in sum(roles.values(), [])], [1, 0, 0, 0]))
        bits = [assignment[v] for v in variables]
        return a, c, graph, base, image, reset, roles, variables, miter, bits

    def test_independent_current_pi_and_original_transition_replay(self):
        a,c,g,b,im,re,roles,variables,miter,bits = self.setup_image()
        record,values = diagnostic.replay_model(a,g,roles,variables,bits,c,miter,"image",runtime.recipe_eval)
        self.assertEqual(record["previous_inputs"], [1])
        self.assertEqual(record["current_inputs"], [0])
        self.assertEqual(record["successor_state"], [1,1])
        self.assertEqual((record["root_value"],record["recipe_value"]), (1,0))
        self.assertFalse(record["reachable_teacher"])
        self.assertEqual(record["domain"], "unrestricted_one_step_image")
        self.assertEqual(values, original_eval(a,[0],[1,1])[0])
        with self.assertRaises(ValueError):
            diagnostic.replay_model(a,g,roles,variables,bits,c,miter,"reset",runtime.recipe_eval)
        with self.assertRaises(ValueError):
            diagnostic.replay_model(a,g,roles,variables,bits,c,miter,"free",runtime.recipe_eval)
        bits[-1] = 1
        with self.assertRaises(ValueError):
            diagnostic.replay_model(a,g,roles,variables,bits,c,miter,"image",runtime.recipe_eval)

    def test_unreachable_image_has_explicit_false_label(self):
        a = attach_step(fixture(0,1,[],[2],[2]))
        c = dict(root=1,recipe=[],out=0)
        g,b,im,re = runtime.compile_graph(a)
        roles,variables = diagnostic.projected_pis(g,b,im,a)
        record,_ = diagnostic.replay_model(a,g,roles,variables,[1],c,im[1],"image",runtime.recipe_eval)
        self.assertFalse(record["reachable_teacher"])
        self.assertEqual(record["successor_state"],[1])

    def test_exhaustive_phase_literal_and_recipe_complements(self):
        a = attach_step(fixture(2,2,[(3,6),(5,8),(10,13)],[11,1],[14,9]))
        candidates = [dict(root=7, recipe=[x, y, internal, 8], out=out)
                      for x,y in ((2,5),(1,6),(0,9))
                      for internal in (-2,-3) for out in (-4,-5)]
        checks = 0
        for c in candidates:
            for phase in ("image","reset"):
                g,b,im,re = runtime.compile_graph(a)
                roles,variables = diagnostic.projected_pis(g,b,im,a)
                mapping = im if phase == "image" else re
                miter = g.xor(mapping[c["root"]],runtime.graph_recipe(g,mapping,c["recipe"],c["out"]))
                for bits in itertools.product((0,1),repeat=len(variables)):
                    assignment = dict(zip(variables,bits))
                    compiled = compiled_eval(g,assignment)
                    if not (compiled[miter//2] ^ (miter%2)):
                        continue
                    row,values = diagnostic.replay_model(a,g,roles,variables,list(bits),c,miter,phase,runtime.recipe_eval)
                    u = [assignment[x//2] for x in roles["previous_inputs"]]
                    pred = [assignment[x//2] for x in roles["previous_state"]]
                    x = [assignment[z//2] for z in roles["current_inputs"]]
                    state = original_eval(a,u,pred)[1] if phase=="image" else [0]*a.nl
                    expected = original_eval(a,x,state)[0]
                    self.assertEqual(values,expected)
                    self.assertEqual(row["recipe_value"],original_recipe(c,expected))
                    self.assertEqual(row["reachable_teacher"],phase=="reset")
                    checks += 1
        self.assertGreater(checks, 500)

    def test_missing_duplicate_nonboolean_and_aliased_projection_rejected(self):
        a,c,g,b,im,re,roles,variables,miter,bits = self.setup_image()
        for bad in (bits[:-1],bits+[0],[True]+bits[1:],[2]+bits[1:],["1"]+bits[1:]):
            with self.subTest(bits=bad), self.assertRaises(ValueError):
                diagnostic.graph_values(g,variables,bad)
        with self.assertRaises(ValueError):
            diagnostic.graph_values(g,[variables[0]]*len(variables),bits)
        with self.assertRaises(ValueError):
            diagnostic.projected_pis(g,b,b,a)
        changed=list(im);changed[1]^=1
        with self.assertRaises(ValueError):
            diagnostic.projected_pis(g,b,changed,a)

    def test_appended_signature_mask_preserves_all_complement_polarities(self):
        original = [0,0b10101,0b11100,0b00111]
        samples = [[0,1,0,1],[0,0,1,1],[0,1,1,0]]
        packed,mask = diagnostic.append_samples(original,31,samples)
        self.assertEqual(mask,255)
        for i,v in enumerate(original):
            self.assertEqual(packed[i]&31,v)
            for j,row in enumerate(samples):
                self.assertEqual((packed[i]>>(j+5))&1,row[i])
                self.assertEqual(((packed[i]^mask)>>(j+5))&1,1-row[i])
        for badmask in (0,2,5,8):
            with self.assertRaises(ValueError): diagnostic.append_samples(original,badmask,[])
        for rows in ([[0,0]], [[0,0,0,True]], [[0,0,0,2]]):
            with self.assertRaises(ValueError): diagnostic.append_samples(original,31,rows)

    def test_partial_unknown_extra_and_corrupt_models_fail_closed(self):
        variants = [
            ("", []),
            ("0,1,0,0.0\n", []),
            ("0,0,0,0.0\n", [{"query":0,"values":[1,0,0,0]}]),
            ("0,1,0,0.0\n", [{"query":0,"values":[1,0,0]}]),
            ("0,1,0,0.0\n", [{"query":0,"values":[1,0,0,1]}]),
            ("0,1,0,0.0\n", [{"query":1,"values":[1,0,0,0]}]),
            ("0,2,0,0.0\n", []),
        ]
        for csv_rows, raw in variants:
            with self.subTest(csv=csv_rows,raw=raw), tempfile.TemporaryDirectory() as tmp:
                a,c,g,b,im,re,roles,variables,miter,bits = self.setup_image()
                def fake(args, **kwargs):
                    Path(args[-2]).write_text("query,result,conflicts,wall_s\n"+csv_rows)
                    Path(args[-1]).write_text("".join(json.dumps(x)+"\n" for x in raw))
                    return SimpleNamespace(returncode=0)
                with mock.patch.object(diagnostic.subprocess,"run",side_effect=fake):
                    with self.assertRaises(ValueError):
                        diagnostic.collect_models(runtime,a,g,b,im,[c],Path(tmp)/"models",Path(__file__),runtime.Deadline(10),{})
        # UNKNOWN without a model contributes no learning row and is counted.
        with tempfile.TemporaryDirectory() as tmp:
            a,c,g,b,im,re,roles,variables,miter,bits = self.setup_image()
            def unknown(args,**kwargs):
                Path(args[-2]).write_text("query,result,conflicts,wall_s\n0,0,0,0.0\n")
                Path(args[-1]).write_text("")
                return SimpleNamespace(returncode=0)
            with mock.patch.object(diagnostic.subprocess,"run",side_effect=unknown):
                samples,report=diagnostic.collect_models(runtime,a,g,b,im,[c],Path(tmp)/"models",Path(__file__),runtime.Deadline(10),{})
            self.assertEqual(samples,[])
            self.assertEqual(report["unknown_skipped"],1)


@unittest.skipUnless(os.environ.get("STRAN2_SOURCE_RUN"),"set STRAN2_SOURCE_RUN for frozen provenance mutations")
class FrozenSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source_run=Path(os.environ["STRAN2_SOURCE_RUN"])
        cls.source=cls.source_run/"045_mem_ctrl"
        cls.job=json.loads((cls.source/"job.json").read_text())
        cls.old=json.loads((cls.source/"chunks/chunk_00000/candidates.json").read_text())
        cls.a=runtime.Aiger(cls.job["case"]["input"])
        cls.g,b,im,re=runtime.compile_graph(cls.a)
        cls.maps=dict(free=b,reset=re,step=im)
        cls.solver=Path(json.loads((cls.source_run/"plan.json").read_text())["solver"])

    def check(self,candidates):
        with tempfile.TemporaryDirectory() as tmp:
            return diagnostic.verify_source(runtime,self.source_run,self.source,self.job,candidates,self.g,self.maps,Path(tmp),self.solver)

    def test_frozen_raw_receipts_reproduce(self):
        bound=self.check(self.old)
        self.assertIn(self.source/"chunks/chunk_00000/obligations.cnf",bound)

    def test_mutated_identity_proof_miter_and_qualification_rejected(self):
        mutations=[
            lambda c:c["proof"].update(step="UNSAT"),
            lambda c:c.update(qualified_offline_opportunity=True),
            lambda c:c["anytime_certificate"].update(input_sha256="0"*64),
            lambda c:c["anytime_certificate"].update(candidate_index=3),
            lambda c:c["anytime_certificate"]["miter_literals"].update(step=0),
            lambda c:c["anytime_certificate"]["receipts"]["step"].update(assumptions=[0]),
            lambda c:c["anytime_certificate"]["receipts"]["step"].update(results_sha256="0"*64),
            lambda c:c["anytime_certificate"]["receipts"]["step"].update(queries_file="../job.json"),
            lambda c:c["anytime_certificate"]["receipts"]["step"].update(row=1),
            lambda c:c["recipe"].__setitem__(0,c["recipe"][0]^1),
        ]
        for i,mutate in enumerate(mutations):
            altered=copy.deepcopy(self.old);mutate(altered[0])
            with self.subTest(mutation=i),self.assertRaises((ValueError,IndexError,KeyError)):
                self.check(altered)


@unittest.skipUnless(os.environ.get("STRAN2_MODEL_SOLVER"),"set STRAN2_MODEL_SOLVER for native helper tests")
class NativeHelperTests(unittest.TestCase):
    def test_model_is_current_after_sat_unsat_sat_and_unused_pi_complete(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)
            (p/"c").write_text("4 1\n1 1\n")
            (p/"q").write_text("4\n0 1 2\n1 1 3\n2 1 0\n3 1 1\n")
            (p/"v").write_text("3\n1 2 3\n")
            command=[os.environ["STRAN2_MODEL_SOLVER"]]+[str(p/x) for x in ("c","q","v","r","m")]
            proc=subprocess.run(command,capture_output=True,text=True,timeout=10)
            self.assertEqual(proc.returncode,0,proc.stderr)
            models=[json.loads(x) for x in (p/"m").read_text().splitlines()]
            self.assertEqual([x["query"] for x in models],[0,1,3])
            self.assertEqual(models[0]["values"][0],1)
            self.assertEqual(models[1]["values"][0],0)
            self.assertTrue(all(len(x["values"])==3 and set(x["values"])<= {0,1} for x in models))

    def test_malformed_requests_and_duplicate_projection_rejected(self):
        for variables,queries in (("2\n1 1\n","1\n0 1 2\n"),
                                 ("1\n0\n","1\n0 1 2\n"),
                                 ("1\n3\n","1\n0 1 2\n"),
                                 ("1\n1\n","1\n1 1 2\n"),
                                 ("1\n1\n","1\n0 1 6\n"),
                                 ("1\n1\n","1\n0 17 2\n")):
            with self.subTest(variables=variables,queries=queries), tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp)
                (p/"c").write_text("3 1\n1 1\n");(p/"q").write_text(queries);(p/"v").write_text(variables)
                command=[os.environ["STRAN2_MODEL_SOLVER"]]+[str(p/x) for x in ("c","q","v","r","m")]
                proc=subprocess.run(command,capture_output=True,text=True,timeout=10)
                self.assertNotEqual(proc.returncode,0)


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def identity(c):
    return c["root"],tuple(c["recipe"]),c["out"]


def independent_artifact_audit(run, frozen_run):
    """Replay all real models independently and recalculate reported statistics."""
    run, frozen_run = Path(run), Path(frozen_run)
    plan=json.loads((run/"plan.json").read_text())
    assert file_sha(HERE/"diagnostic.py")==plan["diagnostic_sha256"]
    assert file_sha(HERE/"model_solver.c")==plan["model_source_sha256"]
    report=[]
    for name in plan["protocol"]["cases"]:
        out=run/name; source=frozen_run/name
        result=json.loads((out/"result.json").read_text())
        assert result["status"]=="COMPLETE",result
        assert result["area_measured"] is False and result["same_budget_claim"] is False
        assert result["root_count"]==32 and result["control_reproduced"] is True
        assert result["elapsed_s"] <= plan["protocol"]["budget_seconds_per_case"]
        job=json.loads((source/"job.json").read_text())
        a=decode_aiger(job["case"]["input"])
        assert file_sha(job["case"]["input"])==job["case"]["input_sha256"]
        rows=[json.loads(x) for x in (source/"root_search.jsonl").read_text().splitlines()][:32]
        old=json.loads((source/"chunks/chunk_00000/candidates.json").read_text())
        failed=[c for c in old if c["proof"]["step"]=="SAT"]
        old_ids=set(map(identity,old))
        models=out/"models"
        provenance=json.loads((models/"provenance.json").read_text())
        for file,key in (("models.cnf","cnf_sha256"),("models.queries","queries_sha256"),("models.variables","variables_sha256")):
            assert file_sha(models/file)==provenance[key]
        expected_sources=[(c["root"],c["recipe"],c["out"]) for c in failed]
        assert [(q["root"],q["recipe"],q["out"]) for q in provenance["query_sources"]]==expected_sources
        assert [q["query"] for q in provenance["query_sources"]]==list(range(len(failed)))
        assert all(q["phase"]=="image" for q in provenance["query_sources"])
        with (models/"results.csv").open() as stream:
            answers=list(csv.DictReader(stream))
        raw=[json.loads(x) for x in (models/"models.jsonl").read_text().splitlines()]
        witnesses=json.loads((models/"replayed_models.json").read_text())
        assert [int(x["query"]) for x in answers]==list(range(len(failed)))
        assert [x["query"] for x in raw]==[int(x["query"]) for x in answers if int(x["result"])==1]
        assert len(raw)==len(witnesses)
        variable_data=list(map(int,(models/"models.variables").read_text().split()))
        assert variable_data[0]==len(variable_data)-1
        variables=variable_data[1:]
        assert len(set(variables))==len(variables)
        roles=provenance["roles"]
        assert set(variables)=={v//2 for role in roles.values() for v in role}
        samples=[]; sample_lookup={}
        for model,witness in zip(raw,witnesses):
            index=model["query"];candidate=failed[index]
            bits=model["values"]
            assert len(bits)==len(variables) and all(type(b) is int and b in (0,1) for b in bits)
            assignment=dict(zip(variables,bits))
            inputs={name:[assignment[lit//2] ^ (lit%2) for lit in literals] for name,literals in roles.items()}
            _,successor,_=original_eval(a,inputs["previous_inputs"],inputs["previous_state"])
            values,_,_=original_eval(a,inputs["current_inputs"],successor)
            root=values[candidate["root"]];replacement=original_recipe(candidate,values)
            assert root != replacement
            assert witness["root_value"]==root and witness["recipe_value"]==replacement
            assert witness["successor_state"]==successor
            assert all(witness[k]==v for k,v in inputs.items())
            assert witness["reachable_teacher"] is False
            assert witness["domain"]=="unrestricted_one_step_image"
            assert witness["query"]==index and identity(dict(zip(("root","recipe","out"),witness["candidate_id"])))==identity(candidate)
            assert witness["source_provenance_sha256"]==file_sha(models/"provenance.json")
            key=tuple(inputs["current_inputs"]+successor)
            if key not in sample_lookup:
                sample_lookup[key]=len(samples);samples.append(values)
            assert witness["sample_index"]==sample_lookup[key]
        model_report=json.loads((models/"report.json").read_text())
        assert model_report["models"]==len(raw)
        assert model_report["unique_domain_samples"]==len(samples)
        assert model_report["duplicate_domain_samples"]==len(raw)-len(samples)
        assert model_report["unknown_skipped"]==sum(int(x["result"])==0 for x in answers)
        assert model_report["conflicts"]==sum(int(x["conflicts"]) for x in answers)
        for file,key in (("results.csv","results_sha256"),("models.jsonl","models_sha256"),("replayed_models.json","replayed_models_sha256")):
            assert file_sha(models/file)==model_report[key]
        random_records=json.loads((out/"random_models.json").read_text())
        random_samples=[]; random_keys=set()
        for r in random_records:
            assert r["domain"]=="unrestricted_one_step_image" and r["reachable_teacher"] is False
            _,state,_=original_eval(a,r["previous_inputs"],r["previous_state"])
            assert state==r["successor_state"]
            values,_,_=original_eval(a,r["current_inputs"],state)
            key=tuple(r["current_inputs"]+state)
            assert key not in random_keys
            random_keys.add(key);random_samples.append(values)
        assert len(random_samples)==len(samples)==result["random"]["samples"]
        # Recover the frozen packed baseline. Validate several lanes with the
        # independent original evaluator before using it to count projections.
        graph,base,step,reset=runtime.compile_graph(a)
        cfg=runtime.Config(**job["config"])
        (free,image,initial),mask=runtime.signatures(graph,[base,step,reset],cfg)
        seq=[im|(re<<cfg.lanes) for im,re in zip(image,initial)]
        for lane in (0,1,31,127,255):
            before=[(free[i]>>lane)&1 for i in range(1,a.ni+a.nl+1)]
            current=[(image[i]>>lane)&1 for i in range(1,a.ni+1)]
            _,state,_=original_eval(a,before[:a.ni],before[a.ni:])
            expected=original_eval(a,current,state)[0]
            assert [(v>>lane)&1 for v in image]==expected
            assert [(v>>lane)&1 for v in initial]==original_eval(a,current,[0]*a.nl)[0]
        projection_summaries={}
        for label,new_samples in (("targeted",samples),("random",random_samples)):
            claimed=json.loads((out/(label+"_projection_counts.json")).read_text())
            assert len(claimed)==len(rows)
            count=0
            for root_record,entry in zip(rows,claimed):
                nodes=[root_record["root"]]+root_record["pool"]
                prior={tuple((seq[n]>>bit)&1 for n in nodes) for bit in range(2*cfg.lanes)}
                learned={tuple(values[n] for n in nodes) for values in new_samples}
                assert entry==dict(root=root_record["root"],ordered_projection_nodes=nodes,
                    baseline_unique=len(prior),learned_unique=len(learned),
                    learned_new_unique=len(learned-prior),duplicate_learned_projection_rows=len(new_samples)-len(learned))
                count+=len(learned-prior)
            projection_summaries[label+"_new_root_pool_rows"]=count
        refined=json.loads((out/"refined_candidates.json").read_text())
        random_candidates=json.loads((out/"random_candidates.json").read_text())
        refined_ids=set(map(identity,refined));random_ids=set(map(identity,random_candidates))
        new=json.loads((out/"new_proofs/candidates.json").read_text())
        assert set(map(identity,new))==(refined_ids|random_ids)-old_ids
        new_proved={identity(c) for c in new if c["qualified_offline_opportunity"]}
        with (out/"new_proofs/obligations.results.csv").open() as stream:
            proof_rows=list(csv.DictReader(stream))
        assert len(proof_rows)==3*len(new)
        for index,c in enumerate(new):
            proof=[int(x["result"]) for x in proof_rows[3*index:3*index+3]]
            assert [int(x["query"]) for x in proof_rows[3*index:3*index+3]]==list(range(3*index,3*index+3))
            assert c["qualified_offline_opportunity"]==(proof==[1,-1,-1])
            w=c["free_witness"];values,_,_=original_eval(a,w["inputs"],w["state"])
            assert values[c["root"]] != original_recipe(c,values)
        assert result["new_candidates"]==len(refined_ids-old_ids)
        assert result["new_qualified"]==len(new_proved&refined_ids)
        assert result["random_new_candidates"]==len(random_ids-old_ids)
        assert result["random_new_qualified"]==len(new_proved&random_ids)
        assert result["retained_old_candidates"]==len(old_ids&refined_ids)
        refuted=sum(any(v[c["root"]]!=original_recipe(c,v) for v in samples) for c in old)
        assert result["old_candidates_refuted"]==refuted
        good={identity(c) for c in old if c["qualified_offline_opportunity"]}
        assert result["known_proved_retained_in_topk"]==len(good&refined_ids)
        for file in ("control_roots.jsonl","refined_roots.jsonl","random_roots.jsonl"):
            observed=[json.loads(x) for x in (out/file).read_text().splitlines()]
            assert [x["root"] for x in observed]==[x["root"] for x in rows]
            totals=Counter()
            for row in observed: totals.update(row["search"])
            arm={"control_roots.jsonl":"control","refined_roots.jsonl":"refined","random_roots.jsonl":"random"}[file]
            assert dict(totals)==result[arm]["stats"]
            assert sum(row["candidates"] for row in observed)==result[arm]["candidates"]
        for path,digest in json.loads((out/"verified_source_hashes.json").read_text()).items():
            assert file_sha(path)==digest
        report.append(dict(case=name,models_replayed=len(raw),unique_image_assignments=len(samples),
            random_assignments_replayed=len(random_samples),free_witnesses_replayed=len(new),
            source_candidates=len(old),source_candidates_refuted=refuted,
            refined_new_candidates=len(refined_ids-old_ids),refined_new_proved=len(new_proved&refined_ids),
            random_new_candidates=len(random_ids-old_ids),random_new_proved=len(new_proved&random_ids),
            **projection_summaries))
    return dict(status="PASS",scope="model/identity/projection/statistics audit only; no area or reachability claim",cases=report)


if __name__ == "__main__":
    if len(sys.argv)>1 and sys.argv[1]=="--audit":
        print(json.dumps(independent_artifact_audit(sys.argv[2],sys.argv[3]),indent=2,sort_keys=True))
    else:
        unittest.main(verbosity=2)
