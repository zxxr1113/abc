#!/usr/bin/env python3
"""Bounded nonlinear-divisor experiment on immutable, ordinary zero-reset AIGER.

No production edit, graph commit, DSEC claim, or additive area attribution.
See protocol.json for the frozen default experiment and proof boundary.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from dataclasses import asdict, dataclass
import csv
import hashlib
import itertools
import json
from pathlib import Path
import random
import socket
import subprocess
import sys
import time
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
sys.path.insert(0, str(PACKAGE / "seq_cut_image"))
from diagnose import Graph, compile_graph  # frozen, independent transition construction
sys.path.insert(0, str(PACKAGE / "teacher_adaptive_tools"))
from teacher_bmc import Aiger

SCHEMA = 1


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, obj):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def require(condition, message):
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class Config:
    pool_cap: int = 24
    reservoir_cap: int = 128
    tfi_depth: int = 6
    peer_hops: int = 1
    alias_cap: int = 8
    max_gates: int = 2
    candidates_per_root: int = 8
    lanes: int = 256
    seed: int = 2026100201
    wall_seconds: float = 120.0

    def validate(self):
        require(2 <= self.pool_cap <= self.reservoir_cap, "pool/reservoir bounds")
        require(self.tfi_depth >= 1 and self.peer_hops in (0, 1), "neighborhood bounds")
        require(self.alias_cap >= 0 and self.max_gates in (1, 2), "search bounds")
        require(self.candidates_per_root > 0 and self.lanes >= 16, "sample/candidate bounds")
        require(self.wall_seconds > 0, "wall_seconds must be positive")


class Deadline:
    def __init__(self, seconds):
        self.start = time.monotonic()
        self.end = self.start + seconds

    def remaining(self):
        value = self.end - time.monotonic()
        if value <= 0:
            raise TimeoutError("case wall budget exhausted")
        return value


class Structure:
    def __init__(self, a):
        self.a = a
        self.nci = a.ni + a.nl
        self.refs = [0] * (a.m + 1)
        self.fanouts = [[] for _ in range(a.m + 1)]
        self.state = [False] + [False] * a.ni + [True] * a.nl
        self.original_hash = {}
        for node, (x, y) in enumerate(a.gates, self.nci + 1):
            for lit in (x, y):
                self.refs[lit // 2] += 1
                self.fanouts[lit // 2].append(node)
            self.state.append(self.state[x // 2] or self.state[y // 2])
            self.original_hash.setdefault(tuple(sorted((x, y))), node)
        for lit in a.outputs + a.latches:
            self.refs[lit // 2] += 1
        self.live = self.tfi([x // 2 for x in a.outputs + a.latches])

    def fanins(self, node):
        return self.a.gates[node - self.nci - 1] if node > self.nci else ()

    def tfi(self, nodes, within=None):
        result, todo = set(), list(nodes)
        while todo:
            node = todo.pop()
            if node in result or (within is not None and node not in within):
                continue
            result.add(node)
            todo.extend(lit // 2 for lit in self.fanins(node))
        return result

    def mffc(self, root):
        return self.dereference(root, set())

    def dereference(self, root, retained):
        """Independent ref-count deletion, after adding references to divisors."""
        require(all(0 < d < root for d in retained), "illegal/cyclic divisor")
        refs = {d: self.refs[d] + 1 for d in retained}
        removed, todo = set(), [root]
        while todo:
            node = todo.pop()
            if node <= self.nci:
                continue
            require(node not in removed, "duplicate dereference")
            removed.add(node)
            for lit in self.fanins(node):
                dep = lit // 2
                refs[dep] = refs.get(dep, self.refs[dep]) - 1
                require(refs[dep] >= 0, "negative reference count")
                if refs[dep] == 0:
                    todo.append(dep)
        return removed

    def cost(self, root, recipe, out):
        used = external_nodes(recipe, out)
        require(all(0 < node < root for node in used), "illegal/cyclic divisor")
        old = self.mffc(root)
        protected = self.tfi(used, old)
        removable = old - protected
        require(removable == self.dereference(root, used), "retention/dereference mismatch")
        return dict(original_mffc=len(old), retained_mffc_nodes=sorted(protected),
                    removable_nodes=sorted(removable), removable=len(removable),
                    fresh_gates=len(recipe) // 2,
                    conservative_gain=len(removable) - len(recipe) // 2)


def external_nodes(recipe, out):
    return {code // 2 for code in list(recipe) + [out] if code >= 2}


def invert(code):
    return code ^ 1 if code >= 0 else -(((-code - 2) ^ 1) + 2)


def recipe_eval(recipe, out, values, mask=1):
    """Evaluate serialized recipe without the formal Graph compiler."""
    require(len(recipe) % 2 == 0, "odd recipe")
    built = []

    def val(code):
        if code >= 0:
            require(code // 2 < len(values), "external literal out of range")
            return values[code // 2] ^ (mask if code & 1 else 0)
        require(code <= -2, "invalid internal code")
        node, phase = divmod(-code - 2, 2)
        require(node < len(built), "forward/cyclic internal reference")
        return built[node] ^ (mask if phase else 0)

    for j in range(0, len(recipe), 2):
        built.append(val(recipe[j]) & val(recipe[j + 1]))
    return val(out)


def normalize(s, root, recipe, out):
    """Simplify and hash against earlier original nodes; remove dead fresh gates.

    An expression reduced to an original literal is Direct and is excluded by
    the caller. Original nodes >= root are never used as divisor shortcuts.
    """
    gates, hashes, mapped = [], {}, []

    def source(code):
        if code >= 0:
            require(code // 2 < root, "illegal original reference")
            return code
        require(code <= -2, "invalid internal code")
        i, phase = divmod(-code - 2, 2)
        require(i < len(mapped), "forward/cyclic internal reference")
        return invert(mapped[i]) if phase else mapped[i]

    def land(x, y):
        if x == 0 or y == 0 or x == invert(y):
            return 0
        if x == 1 or x == y:
            return y
        if y == 1:
            return x
        key = tuple(sorted((x, y)))
        existing = s.original_hash.get(key) if min(key) >= 0 else None
        if existing is not None and existing < root:
            return 2 * existing
        if key not in hashes:
            hashes[key] = -(2 * len(gates) + 2)
            gates.append(key)
        return hashes[key]

    require(len(recipe) % 2 == 0, "odd recipe")
    for j in range(0, len(recipe), 2):
        mapped.append(land(source(recipe[j]), source(recipe[j + 1])))
    output = source(out)
    live = set()
    todo = [output]
    while todo:
        code = todo.pop()
        if code >= 0:
            continue
        node = (-code - 2) // 2
        if node not in live:
            live.add(node)
            todo.extend(gates[node])
    remap = {old: new for new, old in enumerate(sorted(live))}

    def renumber(code):
        if code >= 0:
            return code
        node, phase = divmod(-code - 2, 2)
        return -(2 * remap[node] + phase + 2)

    return [renumber(v) for i in sorted(live) for v in gates[i]], renumber(output)


def graph_recipe(g, mapping, recipe, out):
    built = []

    def val(code):
        if code >= 0:
            return mapping[code // 2] ^ (code & 1)
        require(code <= -2, "invalid recipe")
        node, phase = divmod(-code - 2, 2)
        require(node < len(built), "cyclic recipe")
        return built[node] ^ phase

    for j in range(0, len(recipe), 2):
        built.append(g.land(val(recipe[j]), val(recipe[j + 1])))
    return val(out)


def signatures(g, mappings, config):
    rng = random.Random(config.seed)
    mask = (1 << config.lanes) - 1
    values = [0]
    for gate in g.gates[1:]:
        if gate is None:
            values.append(rng.getrandbits(config.lanes))
        else:
            a, b = gate
            values.append((values[a // 2] ^ (mask if a & 1 else 0)) &
                          (values[b // 2] ^ (mask if b & 1 else 0)))
    return [[values[lit // 2] ^ (mask if lit & 1 else 0) for lit in mapping]
            for mapping in mappings], mask


def make_pool(s, root, mffc, seq, seq_mask, aliases, config):
    """Bounded structural reservoir plus reset/image-equivalent basis aliases.

    Roles have separate quotas so cheap boundary nodes cannot crowd out the
    entire interior, peer, or alias lane. The quota is a fixed global rule.
    """
    distances, todo = {}, deque((lit // 2, 1) for lit in s.fanins(root))
    while todo and len(distances) < config.reservoir_cap:
        node, depth = todo.popleft()
        if node == 0 or node in distances:
            continue
        distances[node] = depth
        if depth < config.tfi_depth:
            todo.extend((lit // 2, depth + 1) for lit in s.fanins(node))
    tfi_nodes = set(distances)
    peers = set()
    if config.peer_hops:
        for node in sorted(tfi_nodes, key=lambda x: (distances[x], x)):
            for peer in s.fanouts[node]:
                if peer >= root:
                    break
                if peer not in tfi_nodes:
                    peers.add(peer)
                if len(peers) >= config.reservoir_cap:
                    break
            if len(peers) >= config.reservoir_cap:
                break
    alias_nodes = set()
    for node in sorted(tfi_nodes | peers):
        signature = min(seq[node], seq[node] ^ seq_mask)
        if signature == 0:
            continue
        count = 0
        for alias in aliases[signature]:
            if alias >= root:
                break
            if alias not in tfi_nodes and alias not in peers:
                alias_nodes.add(alias)
                count += 1
                if count >= config.alias_cap:
                    break
        if len(alias_nodes) >= config.reservoir_cap:
            break
    if config.alias_cap == 0:
        alias_nodes = set()
    sources = defaultdict(set)
    for group, nodes in (("tfi", tfi_nodes), ("peer", peers), ("alias", alias_nodes)):
        for node in nodes:
            sources[node].add(group)
    protected = {node: s.tfi([node], mffc) for node in sources}
    target = seq[root]

    def rank(node):
        value = seq[node]
        # A useful outer AND factor contains all target-1 lanes in some phase.
        usefulness = min(((target ^ polarity) & (~phase & seq_mask)).bit_count()
                         for polarity in (0, seq_mask)
                         for phase in (value, value ^ seq_mask))
        return (len(protected[node]), usefulness,
                min((value ^ target).bit_count(), (value ^ target ^ seq_mask).bit_count()),
                distances.get(node, config.tfi_depth + 1), node)

    groups = {
        "interior": sorted((x for x in tfi_nodes if x in mffc), key=rank),
        "boundary": sorted(tfi_nodes - mffc, key=rank),
        "peer": sorted(peers, key=rank),
        "alias": sorted(alias_nodes, key=rank),
    }
    chosen = []
    quota = max(1, config.pool_cap // len(groups))
    for nodes in groups.values():
        chosen.extend(x for x in nodes[:quota] if x not in chosen)
    remaining = sorted(set(sources) - set(chosen), key=rank)
    chosen.extend(remaining[:max(0, config.pool_cap - len(chosen))])
    chosen = chosen[:config.pool_cap]
    info = {node: dict(roles=sorted(sources[node]), nonlinear=node > s.nci,
                       retained_mffc=len(protected[node]), distance=distances.get(node))
            for node in chosen}
    return sorted(chosen), info, {"reservoir": len(sources),
                                 "role_counts": {k: len(v) for k, v in groups.items()}}


def candidate_key(c):
    return (-c["conservative_gain"], c["fresh_gates"], c["recipe"], c["out"])


def search_root(s, root, pool, pool_info, seq, seq_mask, free, free_mask, config, deadline):
    literals = [(2 * node + phase, seq[node] ^ (seq_mask if phase else 0))
                for node in pool for phase in (0, 1)]
    # Trivial equal/complement signed operands never create an AND Build.
    pairs = [(a, b, sa & sb) for j, (a, sa) in enumerate(literals)
             for b, sb in literals[j + 1:] if a != (b ^ 1)]
    found, seen = {}, set()
    stats = Counter()
    mffc = s.mffc(root)
    positions = {node: bit for bit, node in enumerate(sorted(mffc))}
    protected_masks = {}
    def protected_mask(node):
        if node not in protected_masks:
            protected_masks[node] = sum(1 << positions[v] for v in s.tfi([node], mffc))
        return protected_masks[node]
    worst_key = None

    def accept(recipe, out):
        nonlocal worst_key
        stats["signature_hits"] += 1
        recipe, out = normalize(s, root, recipe, out)
        if not recipe:
            stats["direct_after_hash"] += 1
            return
        identity = tuple(recipe), out
        if identity in seen:
            return
        seen.add(identity)
        if recipe_eval(recipe, out, seq, seq_mask) != seq[root]:
            raise ValueError("signature normalization mismatch")
        difference = recipe_eval(recipe, out, free, free_mask) ^ free[root]
        if not difference:
            stats["no_sampled_free_witness"] += 1
            return
        used = sorted(external_nodes(recipe, out))
        require(all(0 < node < root for node in used), "illegal/cyclic divisor")
        protected = 0
        for node in used:
            protected |= protected_mask(node)
        fresh = len(recipe) // 2
        gain = len(mffc) - protected.bit_count() - fresh
        if gain <= 0:
            stats["nonpositive_retention_gain"] += 1
            return
        if not any(node > s.nci for node in used):
            stats["ci_only_recipe"] += 1
            return
        stats["positive_sampled_candidates"] += 1
        key = (-gain, fresh, recipe, out)
        if worst_key is not None and key >= worst_key:
            return
        cost = dict(original_mffc=len(mffc),
                    retained_mffc_nodes=[node for node, bit in positions.items() if protected >> bit & 1],
                    removable_nodes=[node for node, bit in positions.items() if not (protected >> bit & 1)],
                    removable=len(mffc) - protected.bit_count(),
                    fresh_gates=fresh, conservative_gain=gain)
        # Hashing may introduce earlier nodes not explicitly in the pool.
        roles = {str(node): pool_info.get(node, dict(roles=["hash_reuse"],
                                                    nonlinear=node > s.nci)) for node in used}
        found[identity] = dict(root=root, recipe=recipe, out=out, divisors=used,
                               divisor_roles=roles, witness_lane=(difference & -difference).bit_length() - 1,
                               **cost)
        if len(found) > config.candidates_per_root:
            worst = max(found, key=lambda ident: candidate_key(found[ident]))
            del found[worst]
        if len(found) == config.candidates_per_root:
            worst_key = max(candidate_key(cand) for cand in found.values())

    for a, b, signature in pairs:
        if signature == seq[root]:
            accept([a, b], -2)
        if signature ^ seq_mask == seq[root]:
            accept([a, b], -3)
    if config.max_gates == 2:
        for output_phase in (0, 1):
            target = seq[root] ^ (seq_mask if output_phase else 0)
            for c, sc in literals:
                deadline.remaining()
                if target & (sc ^ seq_mask):
                    continue
                for a, b, first in pairs:
                    if first & sc == target:
                        accept([a, b, -2, c], -(4 + output_phase))
                    if (first ^ seq_mask) & sc == target:
                        accept([a, b, -3, c], -(4 + output_phase))
    ordered = sorted(found.values(), key=candidate_key)
    stats["candidate_cap_dropped"] = stats["positive_sampled_candidates"] - len(ordered)
    # Expensive independent ref-count verification is needed only for retained
    # candidates; fast protected masks above determine exactly the same cost.
    for candidate in ordered:
        independent = s.cost(root, candidate["recipe"], candidate["out"])
        require(all(candidate[k] == value for k, value in independent.items()),
                "cached retention mask differs from independent dereference")
    return ordered, stats


def witness(a, candidate, free):
    lane = candidate["witness_lane"]
    assignment = [(free[i] >> lane) & 1 for i in range(1, a.ni + a.nl + 1)]
    pi, state = assignment[:a.ni], assignment[a.ni:]
    _, _, values = a.step(pi, state)
    actual = values[candidate["root"]]
    replacement = recipe_eval(candidate["recipe"], candidate["out"], values)
    require(actual != replacement, "free witness failed original-graph replay")
    return dict(kind="free_PI_RO", inputs=pi, state=state, root=actual,
                replacement=replacement, replay="PASS", lane=lane)


def run_queries(g, queries, out, solver, deadline):
    cnf, qfile, result = out / "obligations.cnf", out / "obligations.queries", out / "obligations.results.csv"
    clauses = g.cnf(cnf)
    with qfile.open("w") as stream:
        stream.write(f"{len(queries)}\n")
        for i, query in enumerate(queries):
            stream.write(f"{i} {len(query)} " + " ".join(map(str, query)) + "\n")
    start = time.monotonic()
    with (out / "solver.log").open("w") as log:
        process = subprocess.run([str(solver), str(cnf), str(qfile), str(result)],
                                 stdout=log, stderr=subprocess.STDOUT,
                                 timeout=deadline.remaining(), check=False)
    require(process.returncode == 0, f"solver exit {process.returncode}")
    with result.open() as stream:
        rows = list(csv.DictReader(stream))
    require(len(rows) == len(queries), "incomplete solver output")
    require([int(x["query"]) for x in rows] == list(range(len(queries))), "query order mismatch")
    answers = [int(row["result"]) for row in rows]
    require(all(x in (-1, 0, 1) for x in answers), "invalid solver status")
    return answers, dict(queries=len(queries), statuses=dict(Counter(map(str, answers))),
                         conflicts=sum(int(x["conflicts"]) for x in rows),
                         solver_process_wall_s=time.monotonic() - start,
                         solver_reported_wall_s=sum(float(x["wall_s"]) for x in rows),
                         clauses=clauses, variables=len(g.gates),
                         cnf_sha256=sha(cnf), queries_sha256=sha(qfile), results_sha256=sha(result),
                         conflicts_per_query=1000)


def diagnose(case, out, solver, config, abc=None, dsec_seconds=120):
    config.validate()
    deadline = Deadline(config.wall_seconds)
    source = Path(case["input"])
    identity = dict(input=str(source.resolve()), input_sha256=sha(source),
                    solver=str(solver.resolve()), solver_sha256=sha(solver),
                    prototype_sha256=sha(__file__), host=socket.gethostname(),
                    python=sys.version, config=asdict(config),
                    dependencies={str(path.relative_to(PACKAGE)): sha(path) for path in (
                        PACKAGE / "seq_cut_image/diagnose.py",
                        PACKAGE / "seq_care_synthesis/scan_exact_care.py",
                        PACKAGE / "teacher_adaptive_tools/teacher_bmc.py",
                        PACKAGE / "seq_care_synthesis/guide.py",
                        HERE / "product.py")})
    require(identity["input_sha256"] == case["input_sha256"], "input hash mismatch")
    write_json(out / "provenance.json", identity)
    a = Aiger(source)
    require(all(value == 0 for value in a.initial), "zero-reset inputs only")
    s = Structure(a)
    g, base, step, reset = compile_graph(a)
    (free, image, initial), free_mask = signatures(g, [base, step, reset], config)
    seq_mask = (1 << (2 * config.lanes)) - 1
    seq = [image[i] | (initial[i] << config.lanes) for i in range(a.m + 1)]
    aliases = defaultdict(list)
    for node in range(1, a.m + 1):
        aliases[min(seq[node], seq[node] ^ seq_mask)].append(node)
    metrics = Counter()
    candidates = []
    with (out / "root_search.jsonl").open("w") as rootlog:
        for root in range(s.nci + 1, a.m + 1):
            deadline.remaining()
            if root not in s.live or not s.state[root]:
                continue
            mffc = s.mffc(root)
            if len(mffc) < 2:
                continue
            metrics["eligible_roots"] += 1
            pool, info, pool_stats = make_pool(s, root, mffc, seq, seq_mask, aliases, config)
            found, stats = search_root(s, root, pool, info, seq, seq_mask, free, free_mask, config, deadline)
            metrics.update(stats)
            metrics["searched_roots"] += 1
            row = dict(root=root, mffc=len(mffc), pool=pool, pool_info=info,
                       pool_stats=pool_stats, search=dict(stats), candidates=len(found))
            rootlog.write(json.dumps(row, sort_keys=True) + "\n")
            candidates.extend(found)
            if metrics["searched_roots"] % 100 == 0:
                rootlog.flush()
                write_json(out / "progress.json", dict(stage="search", root=root, metrics=dict(metrics),
                                                       wall_s=time.monotonic() - deadline.start))
    write_json(out / "candidates.unproved.json", candidates)
    query_order, queries = [], []
    for index, candidate in enumerate(candidates):
        deadline.remaining()
        candidate["free_witness"] = witness(a, candidate, free)
        for phase, mapping in (("free", base), ("reset", reset), ("step", step)):
            new = graph_recipe(g, mapping, candidate["recipe"], candidate["out"])
            diff = g.xor(mapping[candidate["root"]], new)
            query_order.append(dict(query=len(queries), candidate=index, root=candidate["root"],
                                    phase=phase, miter_literal=diff))
            queries.append([diff])
    write_json(out / "query_order.json", query_order)
    write_json(out / "progress.json", dict(stage="formal_queries", candidates=len(candidates),
                                           queries=len(queries), metrics=dict(metrics),
                                           wall_s=time.monotonic() - deadline.start))
    answers, qstats = run_queries(g, queries, out, solver, deadline)
    qualified = []
    status_names = {-1: "UNSAT", 0: "UNKNOWN", 1: "SAT"}
    for index, candidate in enumerate(candidates):
        fs, rs, ss = answers[3 * index:3 * index + 3]
        candidate["proof"] = dict(free=status_names[fs], reset=status_names[rs], step=status_names[ss],
                                  free_witness_replayed=True,
                                  sequential_relation="PROVED_RESET_IMAGE" if rs == ss == -1 else "NOT_PROVED",
                                  production_seq_proof="NOT_RUN", commit="NOT_RUN", dsec="NOT_RUN",
                                  exact_selected_set_gain=None, main_metric_eligible=False,
                                  native_recipe_novelty="NOT_CHECKED")
        require(fs != -1, "solver UNSAT contradicts independently replayed free witness")
        candidate["qualified_offline_opportunity"] = fs == 1 and rs == ss == -1
        if candidate["qualified_offline_opportunity"]:
            qualified.append(candidate)
    best = {}
    for candidate in qualified:
        root = candidate["root"]
        if root not in best or candidate_key(candidate) < candidate_key(best[root]):
            best[root] = candidate
    write_json(out / "candidates.json", candidates)
    write_json(out / "qualified.json", qualified)
    result = dict(schema=SCHEMA, status="COMPLETE", file=case["file"], family=case.get("family"),
                  input_sha256=identity["input_sha256"], loaded_and=case["loaded_AND"], input_and=a.na,
                  live_and=sum(node > s.nci for node in s.live), metrics=dict(metrics),
                  candidate_count=len(candidates), qualified_candidates=len(qualified),
                  qualified_roots=len(best),
                  overlapping_one_per_root_conservative_potential=sum(x["conservative_gain"] for x in best.values()),
                  potential_is_additive=False, measured_seq_build_gain=None,
                  production_seq_proof="NOT_RUN", commit="NOT_RUN", dsec="NOT_RUN",
                  native_recipe_novelty="NOT_CHECKED", proof_queries=qstats,
                  wall_s=time.monotonic() - deadline.start)
    from product import create_product
    result["product"] = create_product(source, qualified, out, abc, dsec_seconds,
                                         expected_input_sha256=identity["input_sha256"], deadline=deadline)
    result["wall_s"] = time.monotonic() - deadline.start
    result["search_and_proof_wall_s"] = result["wall_s"] - sum(result["product"][key].get("wall_s", 0) for key in ("independent_dsec", "baseline_dsec"))
    write_json(out / "result.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", required=True, help="exact packaged case filename")
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--abc", type=Path, help="optional independent ABC DSEC executable")
    parser.add_argument("--dsec-seconds", type=float, default=120.0)
    for key, value in asdict(Config()).items():
        parser.add_argument("--" + key.replace("_", "-"), type=type(value), default=value)
    args = parser.parse_args()
    config = Config(**{key: getattr(args, key) for key in asdict(Config())})
    config.validate()
    manifest = json.loads((PACKAGE / "cases.json").read_text())
    row = next((row for row in manifest["cases"] if row["file"] == args.case), None)
    if row is None:
        parser.error("unknown packaged case")
    case = dict(row, input=str(PACKAGE / row["first_seq_path"]), input_sha256=row["first_seq_sha256"])
    args.out.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    try:
        result = diagnose(case, args.out, args.solver, config, args.abc, args.dsec_seconds)
        print(json.dumps(result, sort_keys=True))
        return 0
    except BaseException as error:
        status = "TIMEOUT" if isinstance(error, (TimeoutError, subprocess.TimeoutExpired)) else "ERROR"
        result = dict(schema=SCHEMA, status=status, file=args.case, error=repr(error),
                      wall_s=time.monotonic() - start, measured_seq_build_gain=None,
                      proof_status="INCOMPLETE", config=asdict(config))
        progress = args.out / "progress.json"
        if progress.exists():
            result["last_progress"] = json.loads(progress.read_text())
        write_json(args.out / "result.json", result)
        (args.out / "error.log").write_text(traceback.format_exc())
        print(json.dumps(result, sort_keys=True), file=sys.stderr)
        return 124 if status == "TIMEOUT" else 1


if __name__ == "__main__":
    raise SystemExit(main())
