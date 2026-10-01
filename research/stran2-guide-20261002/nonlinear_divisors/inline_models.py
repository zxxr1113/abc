"""Opt-in original-query image models; guidance only, never a proof shortcut.

Only actual step-phase SAT queries emit projected models. Exact conclusive
cross-phase cache hits without such a model retain their proof status and are
reported MODEL_CACHE_MISS. No helper or duplicate SAT query is issued here.
Different original-query models and unavailable cache models may change search
quality relative to the standalone-helper lane.
"""
from __future__ import annotations

from collections import Counter
import copy
import csv
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
import time

from anytime import FrozenQueries, STATUS
import prototype as p
from image_guided import DOMAIN, ImageGuidance, d

RUNTIME = ["nonlinear_divisors/inline_models.py", "nonlinear_divisors/query_model_solver.c",
           "nonlinear_divisors/build_query_model_solver.sh"]


def artifact(directory, name):
    p.require(isinstance(name, str) and Path(name).name == name and name not in (".", ".."),
              "invalid inline artifact name")
    return Path(directory) / name


def graph_cnf_sha256(graph):
    """Hash the exact Graph.cnf serialization without writing another large CNF."""
    h = hashlib.sha256()
    count = 1 + 3 * sum(g is not None for g in graph.gates)
    h.update(f"{len(graph.gates)} {count}\n1 1\n".encode())
    for i, gate in enumerate(graph.gates):
        if gate is not None:
            a, b = gate
            z = 2 * i
            h.update(f"3 {a^1} {b^1} {z}\n2 {a} {z^1}\n2 {b} {z^1}\n".encode())
    return h.hexdigest()



@dataclass(frozen=True, slots=True)
class FrozenProofDag:
    """Private immutable snapshot, bound to the exact pure-Tseitin source CNF."""
    gates: tuple
    variables: tuple
    cnf_sha256: str

    @classmethod
    def capture(cls, graph, variables, expected_sha256):
        # Copy both levels. The live Graph and its list can change later without
        # changing any cached plan's meaning; hash only this frozen snapshot.
        gates = tuple(None if gate is None else tuple(gate) for gate in graph.gates)
        p.require(gates and gates[0] is None, "cone graph constant-zero slot invalid")
        for node, gate in enumerate(gates):
            if gate is not None:
                p.require(len(gate) == 2 and all(type(lit) is int and 0 <= lit < 2*node for lit in gate),
                          "cone graph is not a topological AND DAG")
        variables = tuple(variables)
        p.require(all(type(v) is int and v > 0 for v in variables) and
                  len(set(variables)) == len(variables) and set(variables) ==
                  {node for node, gate in enumerate(gates) if node and gate is None},
                  "cone projection is not the complete distinct PI set")
        frozen = cls(gates, variables, expected_sha256)
        # This canonical serializer has ONLY the constant-zero unit and three
        # equivalence clauses for each AND. Equality to the already bound raw
        # CNF excludes every hidden/nondefinitional restriction.
        p.require(graph_cnf_sha256(frozen) == expected_sha256,
                  "cone frozen DAG does not match exact pure-definitional CNF")
        return frozen


@dataclass(frozen=True, slots=True)
class AssumptionCone:
    graph: FrozenProofDag
    assumptions: tuple
    required_pis: tuple
    gate_order: tuple
    nodes: int


class ConeValidator:
    """Exact fanin-union evaluator; cached plans retain an immutable graph.

    This checks saved SAT assumptions only. It never discharges a proof or
    replaces the two full original-AIG passes and original recipe replay.
    """
    def __init__(self, graph, variables, expected_sha256, deadline=None):
        self.deadline = deadline
        self._check_deadline()
        self.graph = FrozenProofDag.capture(graph, variables, expected_sha256)
        self._check_deadline()
        self._plans = {}
        self.metrics = Counter()

    def _check_deadline(self):
        if self.deadline is not None:
            self.deadline.remaining()

    def plan(self, assumptions):
        self._check_deadline()
        assumptions = tuple(assumptions)
        p.require(assumptions and len(assumptions) <= 16 and
                  all(type(lit) is int and 0 <= lit < 2*len(self.graph.gates) for lit in assumptions),
                  "invalid cone assumptions")
        if assumptions not in self._plans:
            seen, stack = set(), [lit//2 for lit in assumptions]
            visits = 0
            while stack:
                visits += 1
                if visits % 1024 == 0:
                    self._check_deadline()
                node = stack.pop()
                if node in seen:
                    continue
                seen.add(node)
                gate = self.graph.gates[node]
                if node and gate is not None:
                    stack.extend(lit//2 for lit in gate)
            pis, order = [], []
            for node in sorted(seen):
                if not node:
                    continue
                gate = self.graph.gates[node]
                if gate is None:
                    pis.append(node)
                else:
                    x, y = gate
                    order.append((node, x//2, x&1, y//2, y&1))
            self._check_deadline()
            self._plans[assumptions] = AssumptionCone(self.graph, assumptions, tuple(pis), tuple(order),
                                                     len(seen - {0}))
            self.metrics["plans_built"] += 1
            self.metrics["planned_distinct_nodes"] += len(seen - {0})
        return self._plans[assumptions]

    def evaluate(self, variables, bits, assumptions, plan=None):
        assumptions = tuple(assumptions)
        expected_plan = self.plan(assumptions)
        plan = expected_plan if plan is None else plan
        p.require(plan is expected_plan and plan.graph is self.graph and plan.assumptions == assumptions,
                  "cone plan graph/assumption binding mismatch")
        # Validate ALL projected bits, including PIs outside this cone.
        p.require(tuple(variables) == self.graph.variables and all(type(v) is int for v in variables),
                  "cone projected variable binding mismatch")
        p.require(len(bits) == len(variables) and all(type(bit) is int and bit in (0, 1) for bit in bits),
                  "incomplete/non-Boolean cone PI model")
        assignment = dict(zip(variables, bits))
        values = {0: 0}
        for node in plan.required_pis:
            values[node] = assignment[node]
        for node, x, sx, y, sy in plan.gate_order:
            values[node] = (values[x] ^ sx) & (values[y] ^ sy)
        self._check_deadline()
        self.metrics["models_checked"] += 1
        self.metrics["compiled_gate_evaluations"] += len(plan.gate_order)
        self.metrics["compiled_pi_loads"] += len(plan.required_pis)
        return tuple(values[lit//2] ^ (lit&1) for lit in assumptions)


def replay_cone_model(a, validator, roles, variables, bits, candidate, miter, assumptions):
    """Same independent original-transition/recipe replay after cone checking.

    This inline-only wrapper intentionally leaves diagnostic.replay_model and
    the standalone helper's full evaluator unchanged as the reference path.
    """
    p.require(list(assumptions) == [miter], "cone candidate miter/assumption mismatch")
    p.require(all(validator.evaluate(variables, bits, assumptions)), "SAT model violates source miter")
    assignment = dict(zip(variables, bits))
    read = lambda role: [assignment[lit//2] ^ (lit&1) for lit in roles[role]]
    u, state, x = read("previous_inputs"), read("previous_state"), read("current_inputs")
    successor = a.step(u, state)[1]
    values = a.step(x, successor)[2]
    old = values[candidate["root"]]
    new = p.recipe_eval(candidate["recipe"], candidate["out"], values)
    p.require(old != new, "SAT model fails independent original-AIG recipe replay")
    return dict(domain=DOMAIN, reachable_teacher=False, previous_inputs=u,
                previous_state=state, current_inputs=x, successor_state=successor,
                root_value=old, recipe_value=new, replay="PASS"), values


def read_model_batch(directory, reference, expected):
    """Revalidate immutable files even on model-cache reuse, without a solve."""
    manifest_path = artifact(directory, reference["manifest_file"])
    p.require(p.sha(manifest_path) == reference["manifest_sha256"], "inline manifest hash mismatch")
    manifest = json.loads(manifest_path.read_text())
    p.require(manifest["schema"] == 1 and manifest["phase"] == "step" and
              manifest["domain"] == DOMAIN and manifest["reachable_teacher"] is False,
              "wrong inline model phase/domain")
    for key, value in expected.items():
        p.require(manifest[key] == value, "inline binding mismatch: " + key)
    required = {"cnf", "queries", "results", "projection", "models", "candidates", "literals"}
    p.require(set(manifest["artifacts"]) == required, "incomplete inline artifact binding")
    paths = {}
    for key, value in manifest["artifacts"].items():
        paths[key] = artifact(directory, value["file"])
        p.require(p.sha(paths[key]) == value["sha256"], "inline artifact hash mismatch: " + key)
    p.require(manifest["artifacts"]["cnf"]["sha256"] == manifest["cnf_sha256"],
              "inline CNF binding mismatch")
    variables = manifest["variables"]
    p.require(all(type(v) is int and v > 0 for v in variables) and len(set(variables)) == len(variables),
              "invalid inline variable projection")
    projection = "step " + str(len(variables)) + "\n" + " ".join(map(str, variables)) + "\n"
    p.require(paths["projection"].read_text() == projection, "inline projection request mismatch")
    qlines = paths["queries"].read_text().splitlines()
    p.require(qlines and len(qlines) == int(qlines[0]) + 1, "incomplete inline query file")
    queries = [list(map(int, line.split())) for line in qlines[1:]]
    p.require(all(len(q) >= 3 and q[:2] == [i, len(q)-2] for i, q in enumerate(queries)),
              "inline query order/cardinality mismatch")
    with paths["results"].open() as stream:
        results = list(csv.DictReader(stream))
    p.require([int(r["query"]) for r in results] == list(range(len(queries))),
              "incomplete inline result rows")
    answers = [int(r["result"]) for r in results]
    p.require(all(r in STATUS for r in answers), "invalid inline result status")
    models = [json.loads(line) for line in paths["models"].read_text().splitlines()]
    p.require(all(set(m) == {"query", "values"} and type(m["query"]) is int for m in models),
              "invalid inline model record")
    p.require([m["query"] for m in models] == [i for i, answer in enumerate(answers) if answer == 1],
              "missing/extra/reordered inline SAT models")
    p.require(all(len(m["values"]) == len(variables) and
                  all(type(b) is int and b in (0, 1) for b in m["values"]) for m in models),
              "incomplete/non-Boolean inline model")
    return manifest, queries, results, models


def bound_model(receipt, reference, batch):
    manifest, queries, results, models = batch
    p.require(receipt["result"] == "SAT" and receipt["cnf_sha256"] == manifest["cnf_sha256"],
              "inline receipt status/CNF mismatch")
    for kind in ("queries", "results"):
        p.require(receipt[kind + "_file"] == manifest["artifacts"][kind]["file"] and
                  receipt[kind + "_sha256"] == manifest["artifacts"][kind]["sha256"],
                  "inline raw receipt artifact mismatch")
    row, model_row = receipt["row"], reference["model_row"]
    p.require(type(row) is int and 0 <= row < len(queries) and type(model_row) is int and
              0 <= model_row < len(models), "inline receipt/model row out of range")
    p.require(queries[row] == [row, len(receipt["assumptions"])] + receipt["assumptions"] and
              int(results[row]["result"]) == 1 and models[model_row]["query"] == row,
              "inline receipt query/result/model row mismatch")
    return models[model_row]


class InlineFrozenQueries(FrozenQueries):
    def __init__(self, graph, out, solver, deadline, expected_solver_identity=None, *, context):
        super().__init__(graph, out, solver, deadline, expected_solver_identity)
        self.binding = copy.deepcopy(context)
        p.require(set(self.binding) == {"input_sha256", "source_hashes", "solver_sha256", "roles", "variables"},
                  "incomplete inline capture context")
        self.binding["cnf_sha256"] = self.fingerprint
        variables = self.binding["variables"]
        roles = self.binding["roles"]
        p.require(set(roles) == {"previous_inputs", "previous_state", "current_inputs"},
                  "invalid inline frame roles")
        literals = roles["previous_inputs"] + roles["previous_state"] + roles["current_inputs"]
        p.require(all(type(lit) is int and lit >= 2 and not lit & 1 and
                      lit // 2 < len(graph.gates) and graph.gates[lit//2] is None for lit in literals),
                  "inline roles must be uncomplemented graph PIs")
        p.require(variables == [lit//2 for lit in literals] and len(set(variables)) == len(variables) and
                  set(variables) == {i for i, g in enumerate(graph.gates) if i and g is None},
                  "inline frame variables not independent/complete")
        self.snapshot = {key: dict(file=name, sha256=p.sha(self.out / name)) for key, name in
                         [("candidates", "candidates.unproved.json"), ("literals", "query_literals.json")]}

    def _batch(self, queries, phase):
        if phase != "step":
            return super()._batch(queries, phase)
        self.deadline.remaining()
        p.require(p.sha(self.cnf) == self.fingerprint, "immutable proof CNF changed")
        self.check_solver()
        tag = f"{len(self.batches):03d}_{phase}"
        qfile, result = self.out / (tag + ".queries"), self.out / (tag + ".results.csv")
        projection, models = self.out / (tag + ".projection"), self.out / (tag + ".models.jsonl")
        with qfile.open("w") as stream:
            stream.write(f"{len(queries)}\n")
            for i, query in enumerate(queries):
                stream.write(f"{i} {len(query)} " + " ".join(map(str, query)) + "\n")
        variables = self.binding["variables"]
        projection.write_text("step " + str(len(variables)) + "\n" + " ".join(map(str, variables)) + "\n")
        qhash, phash = p.sha(qfile), p.sha(projection)
        start = time.monotonic()
        with (self.out / (tag + ".solver.log")).open("w") as log:
            process = subprocess.run([str(self.solver), str(self.cnf), str(qfile), str(result),
                                      str(projection), str(models)], stdout=log, stderr=subprocess.STDOUT,
                                     timeout=self.deadline.remaining(), check=False)
        p.require(process.returncode == 0, f"solver exit {process.returncode}")
        p.require(p.sha(self.cnf) == self.fingerprint and p.sha(qfile) == qhash and p.sha(projection) == phash,
                  "immutable inline solver input changed")
        self.check_solver()
        with result.open() as stream:
            rows = list(csv.DictReader(stream))
        p.require(len(rows) == len(queries), "incomplete solver batch cannot prove a relation")
        p.require([int(r["query"]) for r in rows] == list(range(len(queries))), "query order mismatch")
        answers = [int(r["result"]) for r in rows]
        p.require(all(answer in STATUS for answer in answers), "invalid solver status")
        rhash = p.sha(result)
        receipts = [dict(cnf_sha256=self.fingerprint, assumptions=list(query),
                         queries_file=qfile.name, queries_sha256=qhash,
                         results_file=result.name, results_sha256=rhash,
                         row=i, result=STATUS[answer], reused=False)
                    for i, (query, answer) in enumerate(zip(queries, answers))]
        artifacts = dict(self.snapshot)
        for key, path in [("cnf", self.cnf), ("queries", qfile), ("results", result),
                          ("projection", projection), ("models", models)]:
            artifacts[key] = dict(file=path.name, sha256=p.sha(path))
        manifest_path = self.out / (tag + ".model_binding.json")
        p.write_json(manifest_path, dict(schema=1, phase="step", domain=DOMAIN, reachable_teacher=False,
            **self.binding, artifacts=artifacts, conflicts_per_query=1000,
            model_origin="same solve as ordinary proof query; no additional SAT solve"))
        reference = dict(manifest_file=manifest_path.name, manifest_sha256=p.sha(manifest_path))
        checked = read_model_batch(self.out, reference, self.binding)
        for model_row, model in enumerate(checked[3]):
            receipt = receipts[model["query"]]
            receipt["inline_image_model"] = dict(reference, model_row=model_row)
            bound_model(receipt, receipt["inline_image_model"], checked)
        batch = dict(phase=phase, queries=len(queries), statuses=dict(Counter(map(str, answers))),
                     solver_process_wall_s=time.monotonic() - start,
                     solver_reported_wall_s=sum(float(r["wall_s"]) for r in rows),
                     conflicts=sum(int(r["conflicts"]) for r in rows),
                     queries_file=qfile.name, queries_sha256=qhash,
                     results_file=result.name, results_sha256=rhash,
                     inline_models_emitted=len(checked[3]), inline_model_binding=reference,
                     additional_model_solver_queries=0)
        self.batches.append(batch)
        self.metrics["actual_queries"] += len(queries)
        self.metrics["solver_conflicts"] += batch["conflicts"]
        self.metrics["solver_process_wall_s"] += batch["solver_process_wall_s"]
        self.metrics["solver_reported_wall_s"] += batch["solver_reported_wall_s"]
        self.metrics["inline_models_emitted"] += len(checked[3])
        self.metrics["additional_model_solver_queries"] += 0
        return answers, receipts

    def solve(self, requests, phase):
        answers, receipts = super().solve(requests, phase)
        if phase == "step":
            checked = {}
            for answer, receipt in zip(answers, receipts):
                reference = receipt.get("inline_image_model")
                p.require(reference is None or answer == 1, "non-SAT receipt carried inline model")
                if answer != 1:
                    continue
                self.metrics["step_sat_requests"] += 1
                if reference is None:
                    self.metrics["step_sat_model_cache_misses"] += 1
                    continue
                key = reference["manifest_file"], reference["manifest_sha256"]
                if key not in checked:
                    checked[key] = read_model_batch(self.out, reference, self.binding)
                bound_model(receipt, reference, checked[key])
                self.metrics["step_sat_model_available_requests"] += 1
        # Parent certificates can be annotated or edited independently; neither
        # their nested file reference nor another receipt may alias our cache.
        return answers, [copy.deepcopy(receipt) for receipt in receipts]


def collect_inline_models(a, original_graph, base, step, candidates, out, job, deadline, identity):
    """Read original proof models, rebuild exact CNF, then replay original AIG."""
    start = time.monotonic()
    deadline.remaining()
    p.require(p.sha(job["case"]["input"]) == job["case"]["input_sha256"], "inline original input changed")
    out.mkdir()
    roles, variables = d.projected_pis(original_graph, base, step, a)
    expected = dict(input_sha256=job["case"]["input_sha256"], source_hashes=job["source_hashes"],
                    solver_sha256=job["solver_sha256"], roles=roles, variables=variables)
    # Rebuild all original chunk miters in their original order, not a separate
    # feedback-only CNF. The replay still evaluates the original AIG separately.
    chunks, batches, witnesses, samples, seen, unavailable = {}, {}, [], [], {}, []
    source_records = []
    for candidate in candidates:
        deadline.remaining()
        proof, cert = candidate["proof"], candidate["anytime_certificate"]
        p.require((proof["free"], proof["reset"], proof["step"]) == ("SAT", "UNSAT", "SAT"),
                  "ineligible inline feedback source")
        p.require(cert["input_sha256"] == expected["input_sha256"] and cert["root"] == candidate["root"] and
                  cert["recipe"] == candidate["recipe"] and cert["out"] == candidate["out"],
                  "inline candidate/certificate binding mismatch")
        name = cert["chunk"]
        chunk = artifact(Path(job["out"]) / "chunks", name)
        receipt = cert["receipts"]["step"]
        p.require(receipt["result"] == "SAT" and receipt["cnf_sha256"] == cert["cnf_sha256"] and
                  receipt["assumptions"] == [cert["miter_literals"]["step"]], "inline step receipt mismatch")
        reference = receipt.get("inline_image_model")
        if reference is None:
            unavailable.append(dict(candidate_id=list(d.candidate_id(candidate)), reason="MODEL_CACHE_MISS",
                                    receipt=copy.deepcopy(receipt)))
            continue
        key = name, reference["manifest_file"], reference["manifest_sha256"]
        if key not in batches:
            batches[key] = read_model_batch(chunk, reference, dict(expected, cnf_sha256=cert["cnf_sha256"]))
        batch = batches[key]
        model = bound_model(receipt, reference, batch)
        if name not in chunks:
            graph = p.Graph()
            graph.gates, graph.hash = list(original_graph.gates), dict(original_graph.hash)
            frozen = json.loads((chunk / "candidates.unproved.json").read_text())
            literals = []
            # compile_graph's reset mapping has independent current PI x too.
            _, _, _, reset = p.compile_graph(a)
            for source in frozen:
                deadline.remaining()
                row = {}
                for phase, mapping in dict(free=base, reset=reset, step=step).items():
                    expression = p.graph_recipe(graph, mapping, source["recipe"], source["out"])
                    row[phase] = graph.xor(mapping[source["root"]], expression)
                literals.append(row)
            p.require(literals == json.loads((chunk / "query_literals.json").read_text()),
                      "inline source miter map mismatch")
            validator = None
            if job.get("inline_cone_check"):
                # Freeze BEFORE hashing, so plans never depend on a mutable Graph.
                deadline.remaining()
                validator = ConeValidator(graph, variables, cert["cnf_sha256"], deadline)
                deadline.remaining()
            else:
                p.require(graph_cnf_sha256(graph) == cert["cnf_sha256"], "inline rebuilt original proof CNF mismatch")
            chunks[name] = graph, frozen, literals, validator
        graph, frozen, literals, validator = chunks[name]
        index = cert["candidate_index"]
        p.require(type(index) is int and 0 <= index < len(frozen) and
                  d.candidate_id(frozen[index]) == d.candidate_id(candidate) and
                  cert["miter_literals"] == literals[index], "inline source candidate index/miter mismatch")
        if validator is None:
            row, values = d.replay_model(a, graph, roles, variables, model["values"], candidate,
                                        literals[index]["step"], "image", p.recipe_eval)
        else:
            deadline.remaining()
            row, values = replay_cone_model(a, validator, roles, variables, model["values"], candidate,
                                           literals[index]["step"], receipt["assumptions"])
            deadline.remaining()
        key = tuple(row["current_inputs"] + row["successor_state"])
        if key not in seen:
            seen[key] = len(samples)
            samples.append(values)
        row.update(candidate_id=list(d.candidate_id(candidate)), sample_index=seen[key],
                   source_chunk=name, source_receipt=copy.deepcopy(receipt),
                   source_proof_candidate_index=index)
        witnesses.append(row)
        source_records.append(dict(chunk=name, candidate_index=index, reference=copy.deepcopy(reference)))
    provenance = dict(**identity, **expected, schema=1, mode="original_ordinary_step_sat",
                      additional_solver_queries=0, query_sources=source_records,
                      model_unavailable=unavailable, reachable_teacher=False, domain=DOMAIN)
    if job.get("inline_cone_check"):
        provenance["compiled_model_validator"] = "exact_assumption_cone_on_immutable_verified_Tseitin_DAG"
    p.write_json(out / "provenance.json", provenance)
    provenance_hash = p.sha(out / "provenance.json")
    for row in witnesses:
        row["source_provenance_sha256"] = provenance_hash
    p.write_json(out / "replayed_models.json", witnesses)
    report = dict(queries=0, additional_solver_queries=0, models=len(witnesses),
                  eligible_step_sat_candidates=len(candidates), model_cache_misses=len(unavailable),
                  unknown_skipped=0, conflicts=0, unique_domain_samples=len(samples),
                  duplicate_domain_samples=len(witnesses)-len(samples), wall_s=time.monotonic()-start,
                  source="original ordinary step-SAT query", raw_model_batches=len(batches),
                  raw_models_emitted=sum(len(batch[3]) for batch in batches.values()),
                  provenance_sha256=provenance_hash,
                  replayed_models_sha256=p.sha(out / "replayed_models.json"))
    if job.get("inline_cone_check"):
        counters = Counter()
        for _, _, _, validator in chunks.values():
            counters.update(validator.metrics)
        report["compiled_model_validator"] = "exact_assumption_cone_on_immutable_verified_Tseitin_DAG"
        report["cone_validation"] = dict(counters)
    p.write_json(out / "report.json", report)
    deadline.remaining()
    return samples, report


class InlineImageGuidance(ImageGuidance):
    def collect(self, sources, target):
        return collect_inline_models(self.a, self.graph, self.base, self.step, sources, target,
            self.job, self.deadline, dict(teacher_version_before=self.version,
                added_domain=DOMAIN, pool_signature_sha256=self.initial_hash))
