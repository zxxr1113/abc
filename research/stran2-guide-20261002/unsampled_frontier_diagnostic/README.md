# Isolated unsampled-difference frontier diagnostic

This is preparation for a separately reviewed, explicitly authorized experiment.
It does not change production, the nonlinear runtime, online search, or STRAN2.md.
No four-case experiment is run by authentication, building, or the synthetic tests.

## Frozen question and scope

The original 256 unrestricted free samples may miss a genuine difference. Keep
the original witnessed top-eight unchanged, and add a separate deterministic
top-eight from the zero-sampled-difference population after the same normalized,
positive retention-cost and nonlinear-divisor gates. Use the existing structural
rank. Never backfill after COMB-UNSAT/UNKNOWN or tune the cap to a known result.

Use only the preserved mem_ctrl/wb_dma/b20_opt/des_area first32 snapshots, their
identical post-FIRST-image-refinement sequence domain, original input graphs,
frozen runtime, ordered pools, grammar and initial256 free domain. Observe three
known mem/root1263 sentinel ranks without inserting any sentinel into the result.
Baseline candidates, metadata, sampled witness and every root counter must
reproduce exactly before accepting any new candidate proof.

Every extra candidate gets an unrestricted free SAT query first. A SAT result
must include every compiled graph PI, exact source/CNF/query/result/model binding,
full compiled DAG validation, independent all-original-node PI/RO simulation,
and root/recipe difference replay. The complete witness belongs to that candidate;
there is no sampled lane and no global free-signature update. Then require reset
UNSAT and unrestricted-image UNSAT with independent prior/current PIs. UNKNOWN
never qualifies or retries. Retain all historical qualified identities in the
cumulative union, with historical proof references clearly separated from fresh
proof. No candidate selection or measured area is produced here.

## Evidence and integrity

`authentication.json` was produced by hash-only verification against the prior
independent review's pinned SHA256. All four snapshot inputs and referenced source
files survived; nothing was recreated or substituted for missing historical data.
The copied `independent_aig.py` is byte-identical to the previously reviewed
free-domain independent parser (SHA256
`cd1610200221c44e6caf02750823de81fe89169b46be59b335e99d964432e8b0`).

The dedicated C helper only changes the old opt-in model solver's projection tag
to `free`; it remains C1000. The isolated builder binds compiler identities,
transitive headers, commands, static library and tools before/after compilation,
and refuses existing outputs. It never rebuilds or replaces ABC/old solvers.

Every result binds its complete output artifact tree. The supervisor requires
the result digest captured in the worker's completion notice. Source/model/raw
receipt drift, changed metadata or incomplete rows fail closed. Failed attempts
and their first logs remain on disk; subsequent attempts need new output paths.

## Hard bound and stopping

One worker, four fixed cases, 120 seconds each from supervisor child launch through
exit, covering imports, authentication, preparation, both searches, complete free
model capture/replay, free-first proof, persisted receipt revalidation, final source
checks and result writes. At most 256 extra free queries and 768 total extra proof
queries per case. The parent kills the complete owned process group at the bound
and rejects results observed after the deadline. Independent post-case acceptance
hashing is reported separately. A timeout stays incomplete; an integrity/error
halts the protocol. No performance claim follows from concurrent unit tests.

Only independently proved additional relations justify a separately authorized
product/Direct/global-structural-alias/same-selected-set/DSEC audit. Sentinel recovery
would reproduce the known local mechanism, not establish new area or broad gain.
No full55 or online expansion, no new proof-theory or native-novelty claim.

## Preparation and execution

Build to a NEW path:

```sh
bash research/stran2-guide-20261002/unsampled_frontier_diagnostic/build_solver.sh /tmp/unsampled-free-solver-user
UNSAMPLED_SOLVER=/tmp/unsampled-free-solver-user python3 -B -m unittest discover \
  -s research/stran2-guide-20261002/unsampled_frontier_diagnostic -p 'test*.py' -v
```

Execution deliberately requires a separate review JSON with status PASS and exact
source-manifest digest, protocol SHA256, solver SHA256 and solver-build-record SHA256,
plus the parent's explicit GO. Neither artifact is manufactured by preparation.

```sh
python3 -B research/stran2-guide-20261002/unsampled_frontier_diagnostic/run.py \
  --solver /tmp/unsampled-free-solver-user --review REVIEW.json \
  --parent-go RUN_FIXED_FIRST32 --out NEW_OUTPUT_DIRECTORY
```

The review's source-manifest digest is the canonical `common.digest` of
`common.source_manifest()`. It excludes generated authentication/validation/build
summary/source-manifest JSON and logs, but includes all implementation, test,
protocol and README sources. The controller binds the reviewed solver/build to
every child and requires prebuild/postbuild consistency.
