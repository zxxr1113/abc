# Nonlinear-divisor research prototype

This directory is isolated research code. It does not modify the production
`&stran2` algorithm. The authoritative research interpretation is in `STRAN2.md`.
Python standard library only; use the packaged query solver and optionally ABC.

## Run

From the repository root:

```sh
bash research/stran2-guide-20261002/build_query_solver.sh /tmp/stran2-query-solver
make ABC_USE_NO_READLINE=1 -j8 abc
export STRAN2_SOLVER=/tmp/stran2-query-solver STRAN2_ABC="$PWD/abc"
for test in test_prototype.py test_independent_review.py test_partial_audit.py test_product_depth2.py; do
  python3 -m unittest discover \
    -s research/stran2-guide-20261002/nonlinear_divisors -p "$test" -v
done

python3 research/stran2-guide-20261002/nonlinear_divisors/prototype.py \
  --case 005_b03.aig --solver /tmp/stran2-query-solver --abc "$PWD/abc" \
  --out /tmp/nonlinear-b03

python3 research/stran2-guide-20261002/nonlinear_divisors/run_batch.py \
  --pilot --solver /tmp/stran2-query-solver --abc "$PWD/abc" \
  --out /tmp/nonlinear-pilot --workers 2
```

Use `--all` in place of `--pilot` for the packaged 55 cases, or `--cases` followed
by exact case filenames. Output directories must not already exist. Defaults:
24 divisors, 128-node reservoirs, depth-6 TFI, one peer hop, up to eight aliases
per signature source, one/two raw AND templates, eight candidates/root,
256-bit signatures per phase, seed 2026100201. `--help` exposes every bound.
The transform budget is 120 seconds/case including reconstruction; each optional
independent baseline/product DSEC has its own 120-second budget. Timeouts and
UNKNOWN are retained. They are never converted into zero gains or proofs.
Do not alter any runtime source while a batch is running.

## What is checked

- Existing divisors come from bounded TFI, nearby peers, and exact reset/image
  signature aliases. Per-role quotas and retained-cone cost limit the pool
- Connected one/two raw-AND shapes are enumerated without truncating the pair
  frontier. Structural hashing can make two raw gates cost one genuinely fresh
  gate; the cost bound applies after normalization
- Every divisor has original ID below the root. Serialized recipe references
  are checked and topological, preventing combinational cycles
- MFFC deletion retains the complete TFI of every used divisor inside the MFFC.
  Fast protected masks are cross-checked by independent reference-count deletion
- Samples only propose recipes. Every retained candidate has a saved free PI/RO
  counterexample independently replayed on the original graph, plus an explicit
  free-state SAT result. Both original-graph reset and unrestricted predecessor
  one-step root-XOR-recipe queries must return UNSAT
- Reset and one-step image cover every reset-reachable state, so this conjunction
  is a complete sufficient root-relation proof, not bounded simulation. Current
  PI are independent of predecessor PI. This stronger image condition can miss
  valid relations requiring deeper reachability reasoning
- Products select disjoint deletion regions while retaining each other’s divisor
  dependencies. Empty-selection and selected-selection replays use the identical
  hash/cleanup builder. Their actual AND difference is the standalone Build gain
- A recipe whose final output hashes/folds to an old node is Direct, even if a
  dead intermediate was temporarily allocated. It is excluded from Build gain
- Optional ABC DSEC checks both baseline replay and product against the immutable
  input. Only clean PASS/PASS fills `validated_standalone_noncomb_build_gain`

Only ordinary dense binary AIGER with zero reset is supported. Extended typed
properties/constraints, nonzero reset and unknown reset are rejected explicitly.

## Evidence and limits

Each run writes source/input/solver hashes, per-root pool and truncation records,
complete candidate recipes and sampled witnesses, CNF/query files and raw solver
CSV/log, exact selection/rejection records, replay/product AIGs, and DSEC logs.
A batch snapshots all runtime sources and checks for source drift. Its summary
reports coverage, loaded-size strata, and removal of the largest contributor.

`overlapping_one_per_root_conservative_potential` is not additive area.
`product.exact_same_selected_set_build_gain` is an actual standalone graph
measurement but remains unvalidated until both DSEC checks pass. Top-level
`measured_seq_build_gain` intentionally stays null: production integration and
matched native-candidate comparison have not been performed. Native ABC already
has nonlinear divisors and one/two-gate shapes; these are not claimed as new.
This experiment varies pool selection/aliases, untruncated pair enumeration,
post-hash charging and candidate-local reset/image proof retrieval. It does not
establish novelty relative to all native recipes or superiority on the 55 cases.

## Extra-cost audit of an interrupted proof prefix

If a TIMEOUT run reached formal queries, its complete solved prefix can be
independently audited without extending candidate discovery:

```sh
python3 research/stran2-guide-20261002/nonlinear_divisors/audit_partial.py \
  --attempt /tmp/nonlinear-pilot/034_b20_opt \
  --out /tmp/nonlinear-b20-partial-audit \
  --solver /tmp/stran2-query-solver --abc "$PWD/abc"
```

The current runtime source and solver hashes must match the original run.
The audit regenerates the complete original CNF/query identity, replays free
witnesses, and only rechecks complete SAT/UNSAT/UNSAT triples in a fresh solver.
It retains all original files unchanged. Extra proof, reconstruction, and DSEC
costs are explicit. `PARTIAL_CERTIFICATE_AUDIT_COMPLETE` does not change the
original TIMEOUT, fill cohort coverage, or establish same-budget success.


## Optional depth-two proof/product audit

The separate `deeper_image.py` tool rechecks saved candidates using reset frames
0 and 1 plus unrestricted image frame 2. Its tests must run in a separate process
against an explicitly frozen completed pilot source tree; do not mix current and
frozen modules in one unittest discovery process:

```sh
STRAN2_FROZEN_PACKAGE=/tmp/nonlinear-pilot/source \
STRAN2_SOLVER=/tmp/stran2-query-solver \
  python3 -m unittest discover \
  -s research/stran2-guide-20261002/nonlinear_divisors -p test_deeper_image.py -v

python3 research/stran2-guide-20261002/nonlinear_divisors/audit_depth2_product.py \
  --source-case /tmp/nonlinear-pilot/005_b03 \
  --proof-dir /tmp/nonlinear-deeper-image/005_b03 \
  --out /tmp/nonlinear-depth2-b03-product \
  --solver /tmp/stran2-query-solver --abc "$PWD/abc"
```

The product bridge regenerates the saved depth-two CNF and queries, performs a
fresh bounded recheck, and attaches a typed certificate bound to the exact input
and original candidate. It never changes the original one-step SAT result.
`product_depth2.py` accepts only the explicit depth-one or depth-two predicates;
the default `product.py` and frozen pilot results remain unchanged. The bridge
reports new-only, old-only, and union products, plus the exact marginal of
removing only depth-two entries from the same union-selected set. All extra work
is separately timed; it does not improve the original same-budget cohort result.
