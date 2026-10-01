# Prepared all55 matched comparison (not executed)

This is an execution protocol and thin orchestration wrapper, not a new results
report. `STRAN2.md` remains the authoritative research report. No real benchmark,
solver, DSEC, or attribution run was launched while preparing this directory.
`tests.log` includes synthetic wave messages from a mocked subprocess test.

## Frozen question and design

Compare ordinary `anytime.py` (no image flag) with exactly the same runtime's
opt-in `--image-model-solver`. The cohort is **all 55 rows, in the original order,
from `cases.json`**. Each first-SEQ input and its original loaded denominator has
its SHA256 and AND count checked and frozen in `protocol.json`. There are 110
planned arm-cases, including every timeout, error, missing checkpoint, DSEC
failure, and resource-admission non-start.

The unchanged configuration is pool 24, reservoir 128, TFI depth 6, peer hops 1,
aliases 8, raw gates 2, candidates/root 8, lanes 256, seed 2026100201,
chunk roots 32. Transform budget: 120 seconds from worker launch through complete
checkpoint receipt/exit/kill. Query solvers remain at 1,000 conflicts per query.
The empty replay and selected product each receive a separate 120-second DSEC
limit after transformation. Checkpoint/hash audit and DSEC time stay separate.

Manifest-order pairs form 28 blocks (the last has one case). Within a block,
run one arm with the existing CLI's two workers, wait for it to finish including
DSEC, then run the other arm on precisely those cases. Alternate the first arm
by block. Thus no ordinary transform directly competes with an image-guided
transform, there is no completion-order-dependent dispatch, and at most two
case workers are active. Case first-arm balance is 28 ordinary-first versus
27 image-first. The host must be quiescent: this wrapper's lock only prevents
another instance of this wrapper, not unrelated jobs.

This reduces interleaving bias, but cannot remove host load, within-wave long-tail
imbalance, time-of-day effects, or the final singleton imbalance. This is one
paired area/coverage experiment, not formal speedup evidence. Do not select or
replace cases after seeing results, retune budgets, or count audit work inside
the transform's 120 seconds.

The inputs are the **saved first-SEQ fixed prefix**. This does not rerun or
establish a strong native joint fixed point, does not establish native recipe
novelty, and makes no raw typed HWMCC or production-integration claim.

## Capacity and immutable evidence

`capacity_basis.json` records a read-only size survey of retained evidence.
The largest observed case was 363,980,669 raw transform bytes, 54,405,616 Direct
attribution bytes, and 3,780,056 whole-original alias audit bytes. Extrapolating
each maximum to all 110 arm-cases is about 43.25 GiB; 25% headroom, copied tools,
and a 4 GiB reserve bring that stress scenario to about 58.5 GiB. **It is neither
an expected total nor a proven upper bound**, and does not alone reject the run.

Admission instead requires storage for the next complete paired block at these
observed maxima plus 25% headroom, all deferred audits from attempted cases, and
a 4 GiB floor. Initial admission also reserves copied tools and small source/input
snapshots (about 6.4 GiB total with current tools). A second-wave emergency guard
can stop even in the middle of a block if external consumption destroys its
reserve. Every boundary also requires 4 GiB `MemAvailable`; RSS was not measured,
and this check is not a memory limit. Output on tmpfs is refused. In particular,
`/tmp` was full during preparation and is unsuitable for this experiment.

An admission stop prints and writes `CAPACITY_STOP`, exits 2, and preserves
remaining rows as `NOT_STARTED`, never zero gain. All artifacts from earlier
attempts remain. The resource checks are boundary checks, not hard allocation
limits or a guarantee against an unusually large case or external disk use.
Monitor disk/memory during execution. No source writes, active-path relocation,
evidence deletion, automatic compression, or automatic resumption are performed.
If storage approaches the floor, parent-managed reversible archival of **fully
audited and reviewed** completed evidence, with a hash-verified round trip and
restoration at the same absolute paths, needs to be arranged before continuing.
Do not delete the sole expanded evidence or move an active run. The wrapper does not implement archive/rematerialization. Explicit resume is
allowed only for intact, hash-matched snapshots after a recorded capacity stop;
a capacity stop is an incomplete frozen-cohort result, not completion.

At transform start, the wrapper copies all required runtime/audit sources,
`cases.json`, both input families, and all three executables into a new disk-backed
output directory. These copies are hash-checked and made read-only. The existing
CLI creates standard per-wave run directories and its own standard frozen-source
copies. Per-case absolute input paths retain the expected `inputs/first_seq` /
`inputs/loaded` layout, so the existing auditors' loaded-denominator binding works.
Only output files are written thereafter; original source changes cannot alter
this snapshot. Source/input/tool hashes are rechecked at every wave boundary.
Keep the whole output root at its original absolute path for audit replay.

## Commands and approval gate

From the repository root, the following is preparation only (no benchmark):

```sh
P=research/stran2-guide-20261002/full_cohort_validation
python3 -B "$P/test_runner.py" -v
# Use a NEW protocol filename after v3 passes; it binds the final reviewed bytes.
python3 -B "$P/run.py" freeze \
  --protocol "$P/protocol.after-v3.json" \
  --solver /tmp/stran2-query-solver \
  --image-model-solver /tmp/stran2-image-model-solver \
  --abc "$PWD/abc"
```

`protocol.json` is the current prepared snapshot, not authorization. Re-freeze
if reviewed source/solver bytes or their locations change. Freeze checks both
input families, fixed defaults, conflict-limit source, and 55 unique case IDs.
The binary hashes establish exact replay identities; source text matching does
not by itself prove a binary was compiled from those sources.

**Only after v3 independent review/validation passes and explicit parent go:**

```sh
P=research/stran2-guide-20261002/full_cohort_validation
OUT=/workspace/shared/stran2-all55-matched-after-v3
python3 -B "$P/run.py" transform \
  --protocol "$P/protocol.after-v3.json" --out "$OUT" \
  --approved-after-v3-review
```

The approval flag is an acknowledgment, not a substitute for actual approval.
The output root must not already exist. Do not run this concurrently with a
pilot, attribution, build, test suite, or other performance-heavy job. Transform
plus two worst-budget DSECs per case wave would be about 5.6 hours before
controller/setup overhead; this is not a total wall bound. Attribution below has
additional enumeration/reconstruction costs outside its proof/DSEC limits.

After resolving a capacity stop, explicitly resume with:

```sh
python3 -B "$P/run.py" resume --out "$OUT" --approved-after-v3-review
```

Resume checks the frozen sources, both input families, executable and protocol
hashes, ledger/execution journal, exact completed-wave metadata, original absolute
output root, and the same lock. It runs only wholly `NOT_STARTED` waves, including
the second arm after a between-arm stop, and never retries an ERROR wave. Any
RUNNING/mixed state, unexpected existing unstarted output/log, or drift is denied
before launch. Invocation and capacity-stop history are retained. An initial
pre-snapshot admission failure cannot resume; use a fresh output after resolving
capacity. A pair split across invocations remains marked in history and has
additional timing/load bias; do not call it a clean timing measurement.

The next command processes existing transforms sequentially with **the unchanged
`audit_online_products.py`, followed by `audit_global_alias_products.py`**:

```sh
python3 -B "$P/run.py" audit --out "$OUT" --approved-after-v3-review
python3 -B "$P/run.py" summarize --out "$OUT"
```

Do not rerun `audit` into the same root: it requires a new audits directory and
never overwrites evidence. Missing transform runs remain missing. Audit failures
are retained, and `summarize` can inspect any partial set without launching work.
Individual standard per-wave directories can also be passed directly to either
existing auditor; their command lines are saved as `*.attempt.json`.

## Metrics and validity

The online run's raw Build-only gain is diagnostic, **not the primary metric**.
First reconstruct the selected proofs, replay all saved free witnesses, and
perform the selected-root bounded matched-grammar Direct audit. Then use the
whole-original structural hash/complement alias audit to demote safe original
output aliases while retaining exact recipe materialization. The reported
corrected gain is `global_hash_corrected_conditional_build_marginal`, calculated
by removing genuinely new Build from the same selected mixed set and checking
both replay products with independent DSEC (exact graph proof reuse is charged
separately and bound by the existing auditor).

`corrected_rows.json` always contains 110 slots. Only cases with both valid
transform statuses and both non-missing corrected audit gains enter the paired
summary. Final global-audit integrity must be PASS. Report paired coverage,
per-arm equal-case percentage of original loaded AND, paired delta in percentage
points, total AND, weighted delta, size buckets, and sensitivity excluding the
largest positive case delta. The complete transform ledger contains search
completion, checkpoints, separate DSEC outcomes, all raw results and timings.
Per-arm transform/Direct/global DSEC statuses and unresolved Direct query counts
remain visible. A separate no-UNKNOWN bounded-Direct sensitivity subset is
reported; the main conditional metric does not claim that UNKNOWN Direct queries
are UNSAT or that all possible Directs were eliminated.
An unexhausted search may have a valid budgeted incumbent; it is not exhaustive
COMPLETE. A baseline incumbent with validated zero gain is distinct from missing.

The Direct grammar and whole-original structural alias check are bounded
counterfactuals, not exhaustive global Boolean Direct elimination or a proof of
optimal area. If only a subset is valid, report precisely that common subset and
the full 55-case missingness, never a cohort-wide unconditional gain.
