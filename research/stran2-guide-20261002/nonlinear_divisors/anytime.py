#!/usr/bin/env python3
"""Optional anytime reset/image experiment; the original runner is unchanged.

A universal 32-root chunk schedules discovery -> proof -> exact safe checkpoint.
Search order, pool, templates, top-k and conflict limit retain Config defaults.
Only complete SAT/UNSAT results are reused, on byte-identical frozen CNF plus
identical assumptions. UNKNOWN is never cached. Reset failures skip later work.
The supervisor accepts checkpoints observed before one total transform deadline;
startup, parsing, signatures, discovery, proof and all reconstruction are inside.
Independent baseline/product DSEC run afterward with separately reported budgets.
A retained product never changes BUDGET_EXHAUSTED into exhaustive COMPLETE.

--image-model-solver explicitly enables replay-checked image-domain feedback.
--inline-image-models instead captures models from original ordinary step queries
with a separate model-capable --solver, avoiding the helper's duplicate solve.
Pool/ranking/aliases and per-root top-k remain at the initial policy; only recipe
construction signatures grow. These image models are not reachable teachers or
proof certificates. Build-only products require a separately timed selected-root
Direct sensitivity audit before interpreting the gain as the main Build metric.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
from dataclasses import asdict
import json
import os
from pathlib import Path
import selectors
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import traceback

sys.dont_write_bytecode = True
from prototype import (Aiger, Config, Graph, HERE, PACKAGE, Structure, compile_graph,
                       graph_recipe, make_pool, require, search_root, sha,
                       signatures, witness, write_json)
from product import create_product, dsec

PILOT = ["005_b03.aig", "044_i2c.aig", "041_des_area.aig", "034_b20_opt.aig",
         "045_mem_ctrl.aig", "060_wb_dma.aig"]
STATUS = {-1: "UNSAT", 0: "UNKNOWN", 1: "SAT"}
RUNTIME = ["nonlinear_divisors/anytime.py", "nonlinear_divisors/prototype.py",
           "nonlinear_divisors/product.py", "seq_cut_image/diagnose.py",
           "seq_care_synthesis/scan_exact_care.py", "seq_care_synthesis/guide.py",
           "teacher_adaptive_tools/teacher_bmc.py"]


class Budget:
    def __init__(self, start, end):
        self.start, self.end = start, end

    def remaining(self):
        remaining = self.end - time.monotonic()
        if remaining <= 0:
            raise TimeoutError("total anytime transform budget exhausted")
        return remaining


def emit(event):
    print(json.dumps(event, sort_keys=True), flush=True)


def file_identity(path):
    stat = Path(path).stat()
    return (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)


def bind_executable(path, expected_hash=None, expected_identity=None):
    """Full byte identity at case boundaries, with metadata stable around SHA."""
    identity = file_identity(path)
    if expected_identity is not None:
        require(identity == tuple(expected_identity), "solver executable identity changed")
    digest = sha(path)
    require(file_identity(path) == identity, "solver executable changed while hashing")
    if expected_hash is not None:
        require(digest == expected_hash, "solver executable SHA changed")
    return identity, digest


class FrozenQueries:
    """Memoize conclusive results for this immutable CNF, never UNKNOWN.

    A duplicate whose first request is UNKNOWN is issued separately. Receipts
    name the actual raw result row even when a later request reuses that row.
    No entries survive a graph change or are loaded from a different chunk.
    """
    def __init__(self, graph, out, solver, deadline, expected_solver_identity=None):
        self.out, self.solver, self.deadline = Path(out), Path(solver), deadline
        if expected_solver_identity is None:
            self.solver_identity, _ = bind_executable(self.solver)
        else:
            self.solver_identity = tuple(expected_solver_identity)
            self.check_solver()
        self.cnf = self.out / "obligations.cnf"
        deadline.remaining()
        self.clauses = graph.cnf(self.cnf)
        self.fingerprint = sha(self.cnf)
        self.variables = len(graph.gates)
        self.cache, self.metrics, self.batches = {}, Counter(), []
        deadline.remaining()

    def check_solver(self):
        # Anchored once to the worker-entry SHA, never recaptured between chunks.
        # This is a metadata drift guard; case entry/exit retain full SHA checks.
        require(file_identity(self.solver) == self.solver_identity, "solver executable identity changed")

    def _batch(self, queries, phase):
        self.deadline.remaining()
        require(sha(self.cnf) == self.fingerprint, "immutable proof CNF changed")
        self.check_solver()
        tag = f"{len(self.batches):03d}_{phase}"
        qfile, result = self.out / (tag + ".queries"), self.out / (tag + ".results.csv")
        with qfile.open("w") as stream:
            stream.write(f"{len(queries)}\n")
            for i, query in enumerate(queries):
                stream.write(f"{i} {len(query)} " + " ".join(map(str, query)) + "\n")
        start = time.monotonic()
        with (self.out / (tag + ".solver.log")).open("w") as log:
            process = subprocess.run([str(self.solver), str(self.cnf), str(qfile), str(result)],
                                     stdout=log, stderr=subprocess.STDOUT,
                                     timeout=self.deadline.remaining(), check=False)
        require(process.returncode == 0, f"solver exit {process.returncode}")
        require(sha(self.cnf) == self.fingerprint, "immutable proof CNF changed during solver")
        self.check_solver()
        with result.open() as stream:
            rows = list(csv.DictReader(stream))
        require(len(rows) == len(queries), "incomplete solver batch cannot prove a relation")
        require([int(r["query"]) for r in rows] == list(range(len(queries))), "query order mismatch")
        answers = [int(r["result"]) for r in rows]
        require(all(answer in STATUS for answer in answers), "invalid solver status")
        qhash, rhash = sha(qfile), sha(result)
        receipts = [dict(cnf_sha256=self.fingerprint, assumptions=list(query),
                         queries_file=qfile.name, queries_sha256=qhash,
                         results_file=result.name, results_sha256=rhash,
                         row=i, result=STATUS[answer], reused=False)
                    for i, (query, answer) in enumerate(zip(queries, answers))]
        batch = dict(phase=phase, queries=len(queries), statuses=dict(Counter(map(str, answers))),
                     solver_process_wall_s=time.monotonic() - start,
                     solver_reported_wall_s=sum(float(r["wall_s"]) for r in rows),
                     conflicts=sum(int(r["conflicts"]) for r in rows),
                     queries_file=qfile.name, queries_sha256=qhash,
                     results_file=result.name, results_sha256=rhash)
        self.batches.append(batch)
        self.metrics["actual_queries"] += len(queries)
        self.metrics["solver_conflicts"] += batch["conflicts"]
        self.metrics["solver_process_wall_s"] += batch["solver_process_wall_s"]
        self.metrics["solver_reported_wall_s"] += batch["solver_reported_wall_s"]
        return answers, receipts

    def solve(self, requests, phase):
        self.check_solver()
        require(sha(self.cnf) == self.fingerprint, "immutable proof CNF changed")
        requests = [tuple(q) for q in requests]
        for query in requests:
            require(query and len(query) <= 16 and all(0 <= x < 2 * self.variables for x in query),
                    "invalid proof assumptions")
        self.metrics["requested_queries"] += len(requests)
        answers, receipts = [None] * len(requests), [None] * len(requests)
        pending = list(range(len(requests)))
        while pending:
            self.deadline.remaining()
            # The CNF hash is deliberately part of every key, even inside one object.
            unique, deferred, seen = [], [], set()
            for index in pending:
                key = self.fingerprint, requests[index]
                if key in self.cache:
                    answers[index], receipt = self.cache[key]
                    receipts[index] = dict(receipt, reused=True)
                    self.metrics["conclusive_cache_hits"] += 1
                elif key in seen:
                    deferred.append(index)
                else:
                    seen.add(key)
                    unique.append(index)
            if unique:
                result, sources = self._batch([requests[i] for i in unique], phase)
                for index, answer, receipt in zip(unique, result, sources):
                    answers[index], receipts[index] = answer, receipt
                    if answer in (-1, 1):
                        self.cache[self.fingerprint, requests[index]] = answer, receipt
                    else:
                        self.metrics["unknown_not_cached"] += 1
            pending = deferred
        self.check_solver()
        return answers, receipts

    def report(self):
        return dict(**self.metrics, cnf_sha256=self.fingerprint, variables=self.variables,
                    clauses=self.clauses, conflicts_per_query=1000, batches=self.batches,
                    cache_scope="identical immutable CNF and exact assumption tuple; SAT/UNSAT only")


def prove_chunk(a, original_graph, mappings, free, candidates, out, solver, deadline, input_hash,
                expected_solver_identity=None, inline_model_context=None):
    """Freeze all candidate miters before issuing any phase or reusing an answer."""
    out.mkdir(parents=True, exist_ok=False)
    graph = Graph()
    graph.gates, graph.hash = list(original_graph.gates), dict(original_graph.hash)
    literals = []
    for candidate in candidates:
        deadline.remaining()
        candidate["free_witness"] = witness(a, candidate, free)
        row = {}
        for phase, mapping in mappings.items():
            new = graph_recipe(graph, mapping, candidate["recipe"], candidate["out"])
            row[phase] = graph.xor(mapping[candidate["root"]], new)
        literals.append(row)
    write_json(out / "candidates.unproved.json", candidates)
    write_json(out / "query_literals.json", literals)
    if inline_model_context is None:
        broker = FrozenQueries(graph, out, solver, deadline, expected_solver_identity)
    else:
        from inline_models import InlineFrozenQueries, d
        roles, variables = d.projected_pis(graph, mappings["free"], mappings["step"], a)
        broker = InlineFrozenQueries(graph, out, solver, deadline, expected_solver_identity,
            context=dict(inline_model_context, roles=roles, variables=variables))
    records = [dict(free="NOT_RUN", reset="NOT_RUN", step="NOT_RUN") for _ in candidates]
    receipts = [{} for _ in candidates]

    def phase(name, indexes):
        answers, sources = broker.solve([[literals[i][name]] for i in indexes], name)
        for index, answer, receipt in zip(indexes, answers, sources):
            records[index][name] = STATUS[answer]
            receipts[index][name] = receipt
        return [index for index, answer in zip(indexes, answers) if answer == (-1 if name != "free" else 1)]

    reset_safe = phase("reset", list(range(len(candidates))))
    free_sat = phase("free", reset_safe)
    require(all(records[i]["free"] != "UNSAT" for i in reset_safe),
            "free UNSAT contradicts independently replayed witness")
    phase("step", free_sat)
    qualified = []
    for i, candidate in enumerate(candidates):
        record = records[i]
        good = record == dict(free="SAT", reset="UNSAT", step="UNSAT")
        skip_reason = ("reset_" + record["reset"].lower()) if record["reset"] != "UNSAT" else (
            "free_" + record["free"].lower() if record["free"] != "SAT" else None)
        candidate["proof"] = dict(**record, skipped_later_obligations_reason=skip_reason, free_witness_replayed=True,
            sequential_relation="PROVED_RESET_IMAGE" if good else "NOT_PROVED",
            production_seq_proof="NOT_RUN", commit="NOT_RUN", dsec="NOT_RUN",
            exact_selected_set_gain=None, main_metric_eligible=False,
            native_recipe_novelty="NOT_CHECKED")
        candidate["qualified_offline_opportunity"] = good
        candidate["anytime_certificate"] = dict(schema=1, input_sha256=input_hash,
            chunk=out.name, cnf_sha256=broker.fingerprint, candidate_index=i,
            miter_literals=literals[i], root=candidate["root"],
            recipe=list(candidate["recipe"]), out=candidate["out"], receipts=receipts[i])
        if good:
            require(all(receipts[i][p]["result"] == record[p] for p in ("free", "reset", "step")),
                    "certificate status mismatch")
            qualified.append(candidate)
    report = broker.report()
    report.update(candidate_count=len(candidates), qualified=len(qualified),
                  reset_sat=sum(r["reset"] == "SAT" for r in records),
                  reset_unknown=sum(r["reset"] == "UNKNOWN" for r in records),
                  reset_reject_skipped_free_and_step=len(candidates) - len(reset_safe),
                  theoretical_unfiltered_queries=3 * len(candidates))
    write_json(out / "candidates.json", candidates)
    write_json(out / "proof_report.json", report)
    deadline.remaining()
    return qualified, report


def publish_checkpoint(source, qualified, out, number, deadline, input_hash, progress):
    """Publish only a fully materialized exact product; no DSEC in this budget."""
    pending = out / "checkpoints" / f"pending_{number:05d}"
    pending.mkdir(parents=True, exist_ok=False)
    product = create_product(source, qualified, pending, abc=None,
                             expected_input_sha256=input_hash, deadline=deadline)
    artifacts = {name: sha(pending / name) for name in
                 ("product.aig", "replay_without_build.aig", "selection.json", "product_result.json")}
    metadata = dict(schema=1, input_sha256=input_hash, progress=dict(progress), product=product,
                    artifacts=artifacts, transform_elapsed_s=time.monotonic() - deadline.start)
    write_json(pending / "checkpoint.json", metadata)
    deadline.remaining()
    target = pending.with_name(f"checkpoint_{number:05d}")
    pending.rename(target)
    # The supervisor's actual receipt time, not this child's claimed timestamp,
    # determines whether publication was inside the total transform budget.
    emit(dict(event="checkpoint", directory=target.name,
              manifest_sha256=sha(target / "checkpoint.json"),
              gain=product["exact_same_selected_set_build_gain"],
              selected_builds=product["selected_builds"]))
    return product


def transform(job):
    case, config = job["case"], Config(**job["config"])
    config.validate()
    require(job["chunk_roots"] > 0, "chunk_roots must be positive")
    require(not job.get("inline_cone_check") or job.get("inline_image_models"),
            "cone validation requires inline image models")
    deadline = Budget(job["start"], job["end"])
    source, out, solver = Path(case["input"]), Path(job["out"]), Path(job["solver"])
    input_hash = sha(source)
    solver_identity, solver_hash = bind_executable(solver, job["solver_sha256"], job["solver_identity"])
    require(input_hash == case["input_sha256"], "input hash mismatch")
    write_json(out / "provenance.json", dict(schema=1, input=str(source.resolve()),
        input_sha256=input_hash, solver_sha256=solver_hash, solver_identity=solver_identity,
        solver_phase_guard="anchored dev/ino/size/mtime_ns/ctime_ns before and after each query/cache call",
        source_hashes=job["source_hashes"],
        config=asdict(config), chunk_roots=job["chunk_roots"], host=socket.gethostname(),
        python=sys.version, native_recipe_novelty="NOT_CHECKED"))
    model_identity = None
    if job.get("image_model_solver"):
        model_identity, _ = bind_executable(job["image_model_solver"],
            job["image_model_solver_sha256"], job["image_model_solver_identity"])
    metrics, timing = Counter(), Counter()
    qualified, checkpoint, chunk_index = [], 0, 0
    progress = dict(stage="baseline_checkpoint", searched_roots=0, proof_completed_chunks=0,
                    discovered_candidates=0, qualified_candidates=0)
    start = time.monotonic()
    publish_checkpoint(source, [], out, checkpoint, deadline, input_hash, progress)
    timing["checkpoint_wall_s"] += time.monotonic() - start
    checkpoint += 1
    start = time.monotonic()
    a = Aiger(source)
    require(all(value == 0 for value in a.initial), "zero-reset inputs only")
    structure = Structure(a)
    graph, base, step, reset = compile_graph(a)
    (free, image, initial), free_mask = signatures(graph, [base, step, reset], config)
    seq_mask = (1 << (2 * config.lanes)) - 1
    seq = [image[i] | (initial[i] << config.lanes) for i in range(a.m + 1)]
    aliases = defaultdict(list)
    for node in range(1, a.m + 1):
        aliases[min(seq[node], seq[node] ^ seq_mask)].append(node)
    timing["initialization_wall_s"] += time.monotonic() - start
    # The optional feedback lane never changes the pool/rank/alias view.
    pool_seq, pool_seq_mask = seq, seq_mask
    guidance = None
    if job.get("image_model_solver") or job.get("inline_image_models"):
        if job.get("inline_image_models"):
            require(not job.get("image_model_solver"), "choose inline capture or standalone helper")
            from inline_models import InlineImageGuidance as ImageGuidance
        else:
            from image_guided import ImageGuidance
        guidance = ImageGuidance(a, graph, base, step, seq, seq_mask, free, free_mask,
            structure, config, job, deadline, model_identity)
    pending, roots_in_chunk, chunk_roots = [], 0, []

    def flush():
        nonlocal pending, roots_in_chunk, chunk_roots, checkpoint, chunk_index, seq, seq_mask
        while True:
            deadline.remaining()
            chunk_start = time.monotonic()
            chunk_dir = out / "chunks" / f"chunk_{chunk_index:05d}"
            if guidance:
                guidance.mark_attempted(pending)
            accepted, report = prove_chunk(a, graph, dict(free=base, reset=reset, step=step),
                free, pending, chunk_dir, solver, deadline, input_hash, solver_identity,
                inline_model_context=(dict(input_sha256=input_hash, source_hashes=job["source_hashes"],
                    solver_sha256=solver_hash) if job.get("inline_image_models") else None))
            timing["proof_wall_s"] += time.monotonic() - chunk_start
            for key in ("requested_queries", "actual_queries", "conclusive_cache_hits", "unknown_not_cached",
                        "reset_sat", "reset_unknown", "reset_reject_skipped_free_and_step",
                        "theoretical_unfiltered_queries", "solver_conflicts", "solver_process_wall_s"):
                metrics[key] += report.get(key, 0)
            if job.get("inline_image_models"):
                for key in ("inline_models_emitted", "additional_model_solver_queries", "step_sat_requests",
                            "step_sat_model_available_requests", "step_sat_model_cache_misses"):
                    metrics[key] += report.get(key, 0)
            qualified.extend(accepted)
            progress.update(stage="checkpoint", proof_completed_chunks=chunk_index + 1,
                            qualified_candidates=len(qualified))
            if guidance:
                progress["image_guidance"] = guidance.report()
            if accepted:
                start = time.monotonic()
                publish_checkpoint(source, qualified, out, checkpoint, deadline, input_hash, progress)
                timing["checkpoint_wall_s"] += time.monotonic() - start
                checkpoint += 1
            write_json(out / "progress.json", dict(**progress, metrics=dict(metrics), timing=dict(timing),
                       transform_elapsed_s=time.monotonic() - deadline.start))
            chunk_index += 1
            if not guidance:
                break
            pending = guidance.refine(chunk_roots, pending, out)
            seq, seq_mask = guidance.seq, guidance.mask
            progress["image_guidance"] = guidance.report()
            progress["discovered_candidates"] += len(pending)
            write_json(out / "progress.json", dict(**progress, metrics=dict(metrics), timing=dict(timing),
                       transform_elapsed_s=time.monotonic() - deadline.start))
            if not pending:
                break
        pending, roots_in_chunk, chunk_roots = [], 0, []

    with (out / "root_search.jsonl").open("w", buffering=1) as rootlog:
        for root in range(structure.nci + 1, a.m + 1):
            deadline.remaining()
            if root not in structure.live or not structure.state[root]:
                continue
            start = time.monotonic()
            mffc = structure.mffc(root)
            if len(mffc) < 2:
                continue
            metrics["eligible_roots"] += 1
            pool, info, pool_stats = make_pool(structure, root, mffc, pool_seq, pool_seq_mask, aliases, config)
            found, stats = search_root(structure, root, pool, info, seq, seq_mask,
                                      free, free_mask, config, deadline)
            metrics.update(stats)
            metrics["searched_roots"] += 1
            timing["search_wall_s"] += time.monotonic() - start
            root_record = dict(root=root, mffc=len(mffc), pool=pool, pool_info=info,
                pool_stats=pool_stats, search=dict(stats), candidates=len(found))
            if guidance:
                guidance.remember_search(root, pool, info, found, stats)
                root_record.update(teacher_version=guidance.version, pool_signature_version=0,
                                   construction_signature_bits=guidance.mask.bit_length())
                guidance.annotate(found)
            rootlog.write(json.dumps(root_record, sort_keys=True) + "\n")
            pending.extend(found)
            chunk_roots.append(dict(root=root, pool=list(pool), pool_info=info))
            roots_in_chunk += 1
            progress.update(stage="search", last_completed_root=root,
                searched_roots=metrics["searched_roots"],
                discovered_candidates=progress["discovered_candidates"] + len(found))
            if roots_in_chunk >= job["chunk_roots"]:
                flush()
        if roots_in_chunk:
            flush()
    require(sha(source) == input_hash, "input changed during transform")
    bind_executable(solver, job["solver_sha256"], solver_identity)
    if guidance:
        if job.get("image_model_solver"):
            bind_executable(job["image_model_solver"], job["image_model_solver_sha256"], model_identity)
        progress["image_guidance"] = guidance.report()
    deadline.remaining()
    result = dict(schema=1, status="COMPLETE", search_complete=True, **progress,
                  metrics=dict(metrics), timing=dict(timing),
                  transform_elapsed_s=time.monotonic() - deadline.start)
    write_json(out / "transform_result.json", result)
    emit(dict(event="terminal", status="COMPLETE"))
    return 0


def worker(path):
    job = json.loads(Path(path).read_text())
    try:
        return transform(job)
    except BaseException as error:
        status = "BUDGET_EXHAUSTED" if isinstance(error, (TimeoutError, subprocess.TimeoutExpired)) else "ERROR"
        out = Path(job["out"])
        write_json(out / "transform_result.json", dict(schema=1, status=status, search_complete=False,
            error=repr(error), transform_elapsed_s=time.monotonic() - job["start"]))
        (out / "error.log").write_text(traceback.format_exc())
        emit(dict(event="terminal", status=status))
        return 124 if status == "BUDGET_EXHAUSTED" else 1


def record_supervisor_failure(out, command, start, error, process, failure_dir=None):
    """Preserve an infrastructure error even when the output filesystem is full.

    The optional fallback defaults to the caller's current working directory;
    it should be on a writable filesystem distinct from a space-limited out.
    """
    failure = dict(schema=1, status="SUPERVISOR_ERROR", error=repr(error),
        error_type=type(error).__name__, errno=getattr(error, "errno", None), traceback=traceback.format_exc(),
        command=list(map(str, command)), out=str(out),
        child_pid=process.pid if process is not None else None,
        child_exit_code=process.returncode if process is not None else None,
        elapsed_s=time.monotonic() - start)
    target = Path(out) / "supervisor_failure.json"
    try:
        write_json(target, failure)
        return str(target)
    except (OSError, ValueError):
        pass
    try:
        fallback = Path.cwd() if failure_dir is None else Path(failure_dir)
        fallback.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix="stran2-supervisor-failure-",
                                         suffix=".json", dir=fallback, delete=False) as stream:
            json.dump(failure, stream, indent=2, sort_keys=True)
            stream.write("\n")
            return stream.name
    except (OSError, ValueError):
        return None  # Preserve/re-raise the original error even if both disks fail.


def supervise(command, out, start, seconds, failure_dir=None):
    """Receive notices before deadline and clean up all owned startup failures."""
    end, notices, terminal, buffer = start + seconds, [], None, b""
    process, selector, log = None, None, None
    exhausted = False
    try:
        try:
            # Fail before launch when the primary log cannot be opened.
            log = (out / "driver.log").open("wb")
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                       start_new_session=True)
            selector = selectors.DefaultSelector()
            selector.register(process.stdout, selectors.EVENT_READ, "stdout")
            selector.register(process.stderr, selectors.EVENT_READ, "stderr")
            while selector.get_map():
                remaining = end - time.monotonic()
                if remaining <= 0:
                    exhausted = True
                    break
                for key, _ in selector.select(remaining):
                    chunk = os.read(key.fileobj.fileno(), 65536)
                    received = time.monotonic()
                    if not chunk:
                        selector.unregister(key.fileobj)
                        continue
                    log.write(chunk)
                    if key.data != "stdout":
                        continue
                    buffer += chunk
                    while b"\n" in buffer:
                        line, buffer = buffer.split(b"\n", 1)
                        try:
                            event = json.loads(line)
                        except (ValueError, UnicodeDecodeError):
                            continue
                        if not isinstance(event, dict):
                            continue
                        if received <= end and event.get("event") == "checkpoint":
                            event["supervisor_observed_elapsed_s"] = received - start
                            notices.append(event)
                        elif received <= end and event.get("event") == "terminal":
                            terminal = event.get("status")
            if exhausted:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            if process.poll() is None:
                if not exhausted:
                    try:
                        process.wait(timeout=max(0.001, end - time.monotonic()))
                    except subprocess.TimeoutExpired:
                        exhausted = True
                        os.killpg(process.pid, signal.SIGKILL)
            process.wait()
        finally:
            # Selector construction/registration and I/O errors are covered too.
            # Kill descendants even if their leader exited and closed its pipes.
            if process is not None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
            if selector is not None:
                selector.close()
            if process is not None:
                process.stdout.close()
                process.stderr.close()
            if log is not None:
                log.close()
    except BaseException as error:
        failure = record_supervisor_failure(out, command, start, error, process, failure_dir)
        if failure and hasattr(error, "add_note"):
            error.add_note("Supervisor failure record: " + failure)
        raise
    status = "ERROR" if terminal == "ERROR" else "BUDGET_EXHAUSTED" if exhausted else terminal or "ERROR"
    if status == "COMPLETE" and process.returncode != 0:
        status = "ERROR"
    return dict(status=status,
                exit_code=process.returncode, observed_checkpoints=notices,
                transform_process_wall_s=time.monotonic() - start,
                hard_transform_budget_s=seconds, boundary="before worker launch through worker exit/kill")


def verify_checkpoint(out, notice, input_hash):
    name = notice["directory"]
    require(name.startswith("checkpoint_") and name[11:].isdigit(), "invalid checkpoint path")
    path = out / "checkpoints" / name
    require(sha(path / "checkpoint.json") == notice["manifest_sha256"], "checkpoint manifest changed")
    metadata = json.loads((path / "checkpoint.json").read_text())
    require(metadata["input_sha256"] == input_hash, "checkpoint input mismatch")
    require(set(metadata["artifacts"]) == {"product.aig", "replay_without_build.aig", "selection.json", "product_result.json"},
            "incomplete checkpoint artifact manifest")
    for artifact, expected in metadata["artifacts"].items():
        require(artifact in {"product.aig", "replay_without_build.aig", "selection.json", "product_result.json"},
                "invalid checkpoint artifact")
        require(sha(path / artifact) == expected, "checkpoint artifact changed")
    product = metadata["product"]
    require(product == json.loads((path / "product_result.json").read_text()), "product metadata mismatch")
    require(product["exact_same_selected_set_build_gain"] == notice["gain"], "gain mismatch")
    baseline, transformed = Aiger(path / "replay_without_build.aig"), Aiger(path / "product.aig")
    require(baseline.na == product["replay_without_build_and"] and transformed.na == product["product_and"] and
            baseline.na - transformed.na == notice["gain"], "checkpoint AND attribution mismatch")
    selection = json.loads((path / "selection.json").read_text())
    require(len(selection["selected"]) == product["selected_builds"], "selected Build count mismatch")
    checked_files, parsed_queries, parsed_results = {}, {}, {}
    def checked(path, expected):
        if path not in checked_files:
            checked_files[path] = sha(path)
        require(checked_files[path] == expected, "proof artifact hash mismatch")
    for candidate in selection["selected"]:
        proof, certificate = candidate["proof"], candidate["anytime_certificate"]
        require(candidate["qualified_offline_opportunity"] and proof["free"] == "SAT" and
                proof["reset"] == proof["step"] == "UNSAT" and proof["free_witness_replayed"],
                "unproved checkpoint candidate")
        require(certificate["input_sha256"] == input_hash and certificate["root"] == candidate["root"] and
                certificate["recipe"] == candidate["recipe"] and certificate["out"] == candidate["out"],
                "certificate candidate binding mismatch")
        chunk_name = certificate["chunk"]
        require(Path(chunk_name).name == chunk_name and chunk_name not in (".", ".."), "invalid proof chunk path")
        chunk = out / "chunks" / chunk_name
        checked(chunk / "obligations.cnf", certificate["cnf_sha256"])
        for phase in ("free", "reset", "step"):
            receipt = certificate["receipts"][phase]
            require(receipt["cnf_sha256"] == certificate["cnf_sha256"] and receipt["result"] == proof[phase] and
                    receipt["assumptions"] == [certificate["miter_literals"][phase]], "certificate receipt mismatch")
            for kind in ("queries", "results"):
                filename = receipt[kind + "_file"]
                require(Path(filename).name == filename and filename not in (".", ".."), "invalid proof artifact path")
                checked(chunk / filename, receipt[kind + "_sha256"])
            qpath, rpath = chunk / receipt["queries_file"], chunk / receipt["results_file"]
            if qpath not in parsed_queries:
                lines = qpath.read_text().splitlines()
                require(len(lines) == int(lines[0]) + 1, "incomplete receipt query file")
                parsed_queries[qpath] = [list(map(int, row.split())) for row in lines[1:]]
            if rpath not in parsed_results:
                with rpath.open() as stream:
                    parsed_results[rpath] = list(csv.DictReader(stream))
            row = receipt["row"]
            query, answer = parsed_queries[qpath][row], parsed_results[rpath][row]
            require(query == [row, len(receipt["assumptions"])] + receipt["assumptions"] and
                    int(answer["query"]) == row and STATUS[int(answer["result"])] == receipt["result"],
                    "receipt does not match raw solver result")
    return path, metadata


def run_case(case, out, source_dir, plan, config, solver, abc, chunk_roots, dsec_seconds):
    out.mkdir(parents=True, exist_ok=False)
    (out / "chunks").mkdir()
    start = time.monotonic()
    job = dict(case=case, config=asdict(config), out=str(out.resolve()), solver=str(solver.resolve()),
               start=start, end=start + config.wall_seconds, chunk_roots=chunk_roots,
               source_hashes=plan["runtime_source_hashes"], solver_sha256=plan["solver_sha256"],
               solver_identity=plan["solver_identity"])
    if plan.get("image_model_solver"):
        for key in ("image_model_solver", "image_model_solver_sha256", "image_model_solver_identity"):
            job[key] = plan[key]
    if plan.get("inline_image_models"):
        job["inline_image_models"] = True
    if plan.get("inline_cone_check"):
        job["inline_cone_check"] = True
    write_json(out / "job.json", job)
    command = [sys.executable, "-B", str(source_dir / "nonlinear_divisors/anytime.py"),
               "--worker-job", str(out / "job.json")]
    driver = supervise(command, out, start, config.wall_seconds)
    result = dict(schema=1, file=case["file"], family=case.get("family"),
                  loaded_and=case["loaded_AND"], input_sha256=case["input_sha256"],
                  status=driver["status"], search_complete=driver["status"] == "COMPLETE",
                  driver=driver, measured_seq_build_gain=None,
                  native_recipe_novelty="NOT_CHECKED", production_integration="NOT_RUN")
    if driver["exit_code"] != 0 and result["status"] == "COMPLETE":
        result.update(status="ERROR", search_complete=False)
    transform_result = out / "transform_result.json"
    if transform_result.exists():
        result["transform"] = json.loads(transform_result.read_text())
    progress = out / "progress.json"
    if progress.exists():
        result["last_completed_chunk"] = json.loads(progress.read_text())
    audit_start = time.monotonic()
    require(sha(case["input"]) == case["input_sha256"], "input changed before independent DSEC")
    bind_executable(solver, plan["solver_sha256"], plan["solver_identity"])
    if plan.get("image_model_solver"):
        bind_executable(plan["image_model_solver"], plan["image_model_solver_sha256"], plan["image_model_solver_identity"])
    if plan.get("image_model_solver") or plan.get("inline_image_models"):
        result["image_guidance_attribution"] = "Build-only checkpoint; separately timed selected-root Direct sensitivity audit REQUIRED"
    require(all(sha(source_dir / name) == digest for name, digest in plan["runtime_source_hashes"].items()),
            "frozen source changed during transform")
    if driver["observed_checkpoints"]:
        # Earliest wins ties. Later global greedy selection may be worse, so
        # retain the measured best immutable artifact, never merge checkpoints.
        notice = max(driver["observed_checkpoints"], key=lambda x: x["gain"])
        path, metadata = verify_checkpoint(out, notice, case["input_sha256"])
        product = dict(metadata["product"])
        result["selected_checkpoint"] = dict(directory=str(path),
            supervisor_observed_elapsed_s=notice["supervisor_observed_elapsed_s"],
            progress=metadata["progress"], gain=notice["gain"],
            kind="POSITIVE_BUILD_PRODUCT" if notice["gain"] > 0 else "EMPTY_REPLAY_BASELINE")
        result["checkpoint_hash_audit_wall_s"] = time.monotonic() - audit_start
        if abc is not None:
            product["baseline_dsec"] = dsec(abc, case["input"], path / "replay_without_build.aig",
                                            out, dsec_seconds, "baseline_dsec")
            product["independent_dsec"] = dsec(abc, case["input"], path / "product.aig",
                                               out, dsec_seconds, "dsec")
            if product["baseline_dsec"]["status"] == product["independent_dsec"]["status"] == "PASS":
                product["validated_standalone_noncomb_build_gain"] = notice["gain"]
        result["product"] = product
    else:
        result["product"] = None
        result["checkpoint_hash_audit_wall_s"] = time.monotonic() - audit_start
    require(sha(case["input"]) == case["input_sha256"], "input changed during independent DSEC")
    result["total_wall_s_including_dsec_and_audit"] = time.monotonic() - start
    write_json(out / "result.json", result)
    return result


def aggregate(rows):
    validated = [r for r in rows if (r.get("product") or {}).get("validated_standalone_noncomb_build_gain") is not None]
    valid = [r for r in validated if r["status"] in ("COMPLETE", "BUDGET_EXHAUSTED")]
    def stats(items):
        gains = [r["product"]["validated_standalone_noncomb_build_gain"] for r in items]
        return dict(cases=len(items), and_gain=sum(gains),
            equal_case_percent=100 * sum(g / r["loaded_and"] for r, g in zip(items, gains)) / len(items) if items else None,
            weighted_percent=100 * sum(gains) / sum(r["loaded_and"] for r in items) if items else None)
    largest = max(valid, key=lambda r: r["product"]["validated_standalone_noncomb_build_gain"], default=None)
    return dict(attempted=len(rows), search_complete=sum(r["search_complete"] for r in rows),
        statuses=dict(Counter(r["status"] for r in rows)),
        checkpoint_products=sum(r.get("product") is not None for r in rows),
        independently_validated=stats(valid),
        validated_checkpoint_but_error_cases=[r["file"] for r in validated if r not in valid],
        positive_validated_cases=[r["file"] for r in valid if r["product"]["validated_standalone_noncomb_build_gain"] > 0],
        largest_contributor=largest["file"] if largest else None,
        excluding_largest_contributor=stats([r for r in valid if r is not largest]),
        by_loaded_size={name: stats([r for r in valid if lo <= r["loaded_and"] < hi]) for name, lo, hi in
            [("lt1k", 0, 1000), ("1k_to_10k", 1000, 10000), ("10k_to_100k", 10000, 100000), ("ge100k", 100000, float("inf"))]},
        partial_search_is_complete=False, missing_data_are_zero=False,
        scope="standalone reset-image products; native novelty/production comparison NOT_RUN")


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--worker-job":
        return worker(sys.argv[2])
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--case")
    selection.add_argument("--pilot", action="store_true")
    selection.add_argument("--cases", nargs="+")
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--abc", type=Path)
    parser.add_argument("--inline-cone-check", action="store_true",
                        help="opt-in exact assumption-cone validation; requires --inline-image-models")
    guidance_mode = parser.add_mutually_exclusive_group()
    guidance_mode.add_argument("--inline-image-models", action="store_true",
                        help="capture original ordinary step-SAT models with the separate model-capable --solver; never re-solve")
    guidance_mode.add_argument("--image-model-solver", type=Path,
                        help="opt-in image-only guidance with frozen initial pools; requires separate Direct sensitivity audit")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--chunk-roots", type=int, default=32)
    parser.add_argument("--dsec-seconds", type=float, default=120.0)
    for key, value in asdict(Config()).items():
        parser.add_argument("--" + key.replace("_", "-"), type=type(value), default=value)
    args = parser.parse_args()
    require(args.workers > 0 and args.chunk_roots > 0 and args.dsec_seconds > 0, "positive execution bounds required")
    require(not args.inline_cone_check or args.inline_image_models, "cone validation requires inline image models")
    config = Config(**{key: getattr(args, key) for key in asdict(Config())})
    config.validate()
    manifest = json.loads((PACKAGE / "cases.json").read_text())
    names = PILOT if args.pilot else args.cases or [args.case]
    require(len(set(names)) == len(names), "duplicate cases")
    rows = {r["file"]: r for r in manifest["cases"]}
    require(set(names) <= set(rows), "unknown case")
    args.out = args.out.resolve()
    args.out.mkdir(parents=True, exist_ok=False)
    source_dir = args.out / "source"
    runtime = list(RUNTIME)
    if args.image_model_solver or args.inline_image_models:
        from image_guided import RUNTIME as IMAGE_RUNTIME
        runtime.extend(IMAGE_RUNTIME)
    if args.inline_image_models:
        from inline_models import RUNTIME as INLINE_RUNTIME
        runtime.extend(INLINE_RUNTIME)
    for name in runtime:
        target = source_dir / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(PACKAGE / name, target)
    solver_identity, solver_hash = bind_executable(args.solver)
    plan = dict(schema=1, algorithm="anytime_reset_image_v2", cases=names, config=asdict(config),
        chunk_roots=args.chunk_roots, workers=args.workers, dsec_seconds=args.dsec_seconds,
        runtime_source_hashes={name: sha(source_dir / name) for name in runtime},
        solver=str(args.solver.resolve()), solver_sha256=solver_hash, solver_identity=solver_identity,
        abc=str(args.abc.resolve()) if args.abc else None, abc_sha256=sha(args.abc) if args.abc else None,
        host=socket.gethostname(), manifest_sha256=sha(PACKAGE / "cases.json"),
        transform_budget_boundary="before each worker launch through exit/kill; includes all checkpoint products",
        dsec_boundary="two independent checks after transform; each has its own limit",
        original_mode_and_evidence="UNCHANGED", native_recipe_novelty="NOT_CHECKED")
    if args.image_model_solver:
        model_identity, model_hash = bind_executable(args.image_model_solver)
        plan.update(algorithm="anytime_image_guided_frozen_pool_v3",
            image_model_solver=str(args.image_model_solver.resolve()),
            image_model_solver_sha256=model_hash, image_model_solver_identity=model_identity,
            image_model_solver_guard="full SHA at bound case entry/exit and controller validation; anchored dev/ino/size/mtime_ns/ctime_ns around every invocation",
            pool_policy="immutable initial signatures, ranks and aliases",
            construction_policy="append independently replayed unrestricted-one-step-image constraints; restart changed-projection roots in current chunk",
            unchanged_projection_policy="skip discovery only when complete target+frozen-pool projection set is unchanged; retain every accepted global sample",
            reachable_teacher=False, direct_sensitivity_audit="REQUIRED; outside transform, separately timed")
    if args.inline_image_models:
        plan.update(algorithm="anytime_inline_image_models_v1", inline_image_models=True,
            pool_policy="immutable initial signatures, ranks and aliases",
            construction_policy="append replayed models from original ordinary step-SAT queries",
            model_cache_miss_policy="retain proof SAT; skip feedback as MODEL_CACHE_MISS; never re-solve",
            trajectory_policy="original-query models and model-less cache hits may change quality from helper v3",
            reachable_teacher=False, additional_model_solver_queries=0,
            direct_sensitivity_audit="REQUIRED; outside transform, separately timed")
    if args.inline_cone_check:
        plan.update(algorithm="anytime_inline_image_models_cone_v1", inline_cone_check=True,
            compiled_model_validator="exact_assumption_cone_on_immutable_verified_Tseitin_DAG",
            original_aig_and_recipe_replay="UNCHANGED; both full original-AIG passes remain mandatory")
    write_json(args.out / "plan.json", plan)
    results = []
    def work(name):
        row = rows[name]
        case = dict(row, input=str(PACKAGE / row["first_seq_path"]), input_sha256=row["first_seq_sha256"])
        return run_case(case, args.out / Path(name).stem, source_dir, plan, config, args.solver,
                        args.abc, args.chunk_roots, args.dsec_seconds)
    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {executor.submit(work, name): name for name in names}
        for future in as_completed(futures):
            name = futures[future]
            try:
                result = future.result()
            except BaseException as error:
                result = dict(file=name, status="ERROR", search_complete=False, error=repr(error), product=None)
                (args.out / (Path(name).stem + ".controller_error.log")).write_text(traceback.format_exc())
            results.append(result)
            results.sort(key=lambda r: names.index(r["file"]))
            write_json(args.out / "results.json", results)
            summary = aggregate(results)
            if args.image_model_solver or args.inline_image_models:
                summary.update(gain_attribution="raw Build-only checkpoint before selected-root Direct sensitivity",
                    main_metric_status="NOT_ESTABLISHED_UNTIL_SEPARATE_DIRECT_SENSITIVITY_AUDIT",
                    direct_sensitivity_audit="REQUIRED; outside transform, separately timed")
            write_json(args.out / "summary.json", summary)
            emit(dict(file=name, status=result["status"],
                      validated_gain=(result.get("product") or {}).get("validated_standalone_noncomb_build_gain")))
    write_json(args.out / "source_integrity.json", dict(status="PASS" if all(
        sha(source_dir / name) == digest for name, digest in plan["runtime_source_hashes"].items()) else "FAIL"))
    return 0 if all(r["status"] in ("COMPLETE", "BUDGET_EXHAUSTED") for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
