# Standalone free-domain state API

`free_state.py` has no imports from, or edits to, the nonlinear runtime. This is
state/provenance plumbing only. It does not perform candidate enumeration,
formal solving, selection, checkpoint publication, or an online pilot.

## Ownership and bounds

- `FrozenOriginalAig.from_file(path, expected_sha256)` decodes an ordinary
  zero-reset original AIG, verifies the file before/after parsing, and copies
  graph fields into immutable tuples
- `FreeDomainState(graph, signatures, mask, FreeConfig())` is disabled by
  default. Initialization independently replays all original 256 free lanes
- `FreeConfig(enabled=True, max_added_worlds=256)` explicitly enables append.
  The global limit may be lowered, never raised above 256. Each call accepts at
  most 256 source models, matching a fixed 32-root/top-eight proof block
- Disabled `append_verified_models` does not inspect its argument or mutate
  any state. A future mode-off runtime should avoid constructing this object
  at all if initialization overhead matters
- The object owns only free signatures, versions, exact world deduplication,
  and appended-lane provenance. It has no seq array, pool, attempted set, or
  qualified-candidate collection to modify

Every supplied enabled batch is validated in full before mutation, including
rows beyond the append cap. Exact duplicates of original or already-appended
PI/RO worlds do not consume capacity. Distinct worlds enter in canonical source
order. Cap-rejected worlds never cause a replacement, eviction, lane reorder,
or mask wrap. Reaching the cap does not mean that the search is complete.

The implementation retains one packed full-node signature vector and streams
node-value replay; it does not retain one full-node vector per model. PI/RO
worlds and accepted records currently use immutable Boolean tuples, not a
bit-packed storage optimization. They are bounded but add Python object/reference
memory. Peak RSS and runtime overhead have not been measured.

## Source model contract

The caller must already authenticate the original CNF, exact assumption,
solver/model files, and source candidate with the existing model collector.
This module does not open or authenticate receipt files and cannot manufacture
a formal certificate from metadata saying SAT or PASS.

Each row contains:

- `domain="unrestricted_one_step_image"`, `reachable_teacher=false`,
  `replay="PASS"`
- Complete Boolean `previous_inputs`, `previous_state`, `current_inputs`, and
  `successor_state`; optional saved root/recipe values are checked when present
- `free_pi_field`, if supplied, must be `previous_inputs`
- A `provenance` object with `input_sha256`, `source_provenance_sha256`,
  `models_sha256`, `candidate_id=[root,recipe,out]`, and nonnegative integer
  `source_query`, `model_index`, `source_chunk_index`, `source_candidate_index`
- `source_order` must equal the tuple of source chunk, source candidate and
  model index, and be strictly increasing within and across calls
- `receipt` contains CNF/query/result/solver SHA256 bindings, exact single
  `assumptions`, `result="SAT"`, and `row=source_query`

The module checks types, lengths, frame selection, provenance/index consistency,
original-input identity and recipe topology. It replays the transition from the
saved predecessor and independently checks the original source image miter at
its independent current PI. Only the predecessor PI and predecessor RO values
are appended to the free domain. The current PI and successor are used for
source replay, never mistaken for the appended world.

## Snapshots, witnesses and search-cache hints

- `snapshot()` returns immutable signatures, mask, free version, initial-domain
  hash, lane records, and last processed source order. `to_dict()` produces a
  detached JSON-serializable copy. There is no checkpoint restore API yet
- Version increments once per batch that adds at least one world. Duplicate or
  cap-only batches may advance the last processed source order without changing
  free version or domain hash. Existing signature bits never change
- `witness(root, recipe, out, lane=None, snapshot=None)` selects or verifies an
  absolute lane, replays every original node at its complete PI/RO assignment,
  and binds the target candidate, graph hash, free version/hash and source
  origin. Earlier snapshots remain valid. No lane is interpreted modulo 256
- `domain_projection(...)` captures exact sequence and free row sets on the
  ordered `(root, pool...)` nodes. `can_reuse_search(previous)` requires the
  same original graph, exact ordered nodes, and unchanged sets in **both**
  domains. A change in either domain prevents this reuse
- This helper does not replace the runtime's other cache guards: frozen pool
  metadata, normalization/cost/search configuration, completed top-k result,
  and all returned identities already attempted must still match

The future runtime must retain its established qualified union independently.
In the saved positive case that is 49 old plus 3 new = 52 identities; one-shot
B's top-k contains only 51 because it displaced an already proved old identity.
The separate qualified-union audit verifies preservation, identical Direct
scope, and byte-identical B/union products; this module itself does not manage
that collection.

## Tests

```sh
STRAN2_FREE_DIAGNOSTIC_RUN="$PWD/research/stran2-guide-20261002/free_domain_diagnostic/runs/diagnostic-v1" \
python3 -B -m unittest discover \
  -s research/stran2-guide-20261002/free_domain_diagnostic -p 'test*.py' -v
```

The full run has 32 passing tests. The optional saved-model test replays all
420 original model assignments and reproduces the exact four saved B-domain
hashes and ordered world origins. Without the environment variable that one
test explicitly skips; the synthetic state and earlier diagnostic/product
tests still run. Synthetic tests cover default disablement, atomic rejection,
wrong frames/domains and malformed assignments, input/query/source-order
bindings, world dedup/cap/order, immutable caller data and snapshots, stable
appended witnesses, original-graph and ordered-pool cache binding, dual-domain
projection changes, and external seq/qualified-set preservation.
