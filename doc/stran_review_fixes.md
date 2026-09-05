# Review fixes and paired experiment

User authorization: fix the three confirmed review findings and fully compare
stran2 with stran before deciding further optimization directions.

## Changes

- Stage 3 bounds literal coverage by the maximum remaining pair coverage,
  rather than assuming both frontiers share the same coverage maximum.
- Stage 5 permits an exact one-gate residual leaf when one gate remains.
  A pending alternate second pivot cannot be bypassed by this base case.
- Every closure wave, including its final unsuccessful attempt, emits the
  ordinary time, summary, proof-origin, proof-lane, and selected histograms.
  It has scope=closure in schema 8 and does not recount generated/proved work.
- A separate commit-phase matrix preserves the distinction between proof
  origin and actual commit phase. Ordered Seq Build gain now includes every
  SEQ commit's Build marginal contribution. Cleanup gain beyond the total
  marginal contribution is reported separately, not silently assigned to Build.
- The parser checks contiguous AND boundaries and complete time/kind records;
  the runner checks the independently written final AIG against those totals.

Proof policy, teaching signatures, q/j/w, E5 logic, DAG cost policy, root
stopping, and production multipath settings are unchanged.

## Regressions

Built-in tests include the skewed a|(b&c) Stage-3 counterexample and the full
a&b&c truth table at a two-gate limit. All returned recipes are verified, and
cache/profiling/resume modes are compared. Restoring the one-gate base case
makes two old negative-cache fixtures solvable; they now use an XOR residual
which genuinely needs more than one AND gate. Failure-hit assertions remain.

Four parser tests cover closure accumulation, zero-commit closure, extra
cleanup gain, duplicate/missing records, final-output mismatch, and schema-5
compatibility. cal103 on fixed stran2 passed DSEC and final-AIG accounting:
17 closure attempts, 30 closure selections, 54 closure AND gain.

## Full matrix

- Closure-only baseline: detached worktree abc-stran2-review-before,
  commit 24eaa6bd0. Search behavior remains that of merged 2b19e5f3.
- Fixed candidate: branch codex/stran2-review-fixes, source change 967fd94da
  (later script/doc-only commits may appear in the run metadata).
- Both versions run scorr-stran and integrated stran2: four complete groups.
- Identical Q4/W8/q10/j5/w8/C1000/b100/V0/E5/-p; standalone scorr args empty.
- Fixed historical-all-PASS corpus non_timeout_20260904/bitlevel, 268 inputs.
  This preselected corpus has survivor bias and is not the whole benchmark.
- Per-command timeout 1800 s. Because baseline has two invocations, timeout
  counts are not an equal-deadline comparison; report matched PASS times.
- Four groups of 32 workers, aggregate 128. Preflight at 11:14 UTC: load 3.01,
  about 995 GiB available RAM, /tmp full, /dev/shm 504 GiB available; no active
  ABC jobs from other tasks. Use TMPDIR=/dev/shm/stran2-review-fixes-20260905.
- Large batch skips DSEC explicitly; representative cal103 DSEC is separate.
- Raw CSV destination: script2/experiment_reports/20260905_stran2_review_fixes.
- Reusable runtime scripts: script2/stran2_review_fixes, versioned copies under
  scripts/stran2_review_fixes. Preserve other tasks' scripts and binaries.

Acceptance and analysis: inspect all failure statuses, require 268 rows/group,
match input hashes, compare wall/user totals and geometric means, final
AND/latches and better/equal/worse, complete SEQ gain and ordered SEQ Build
gain normalized by input ANDs, candidate counts, closure contribution, and
time breakdown. Do not infer correctness from PASS/SKIP or from equal counts.

## Completed results

The four groups finished on 2026-09-05 at about 11:27 UTC. All 268 inputs in
each group have matching input hashes and PASS scorr/stran status. Across
1,072 rows: timeout=0, assertion=0, ABC error=0, profile error=0,
missing/malformed output=0, and DSEC failure=0 with DSEC SKIP=1,072.
Separate fixed-stran2 DSEC audits passed on cal103 and fib_05 (2 audited).
PASS in the full matrix is execution/accounting success, not formal equivalence.

All four runs used clean trees. Fixed run commit:
45a89cbdb9644b62c923bf5d58890c15dc05f5c6. Binary SHA256:
e7e3a9c6bedc623a6cd3fe0cbfd10728a1ac401b75f98fd767f069a39ae7d7b5.
Baseline binary SHA256:
f508f0af78247dee22879e479e69255fd83b97756416af9436980215f95f17ba.
The raw rows also record runner/parser hashes and input manifest identity.
Later documentation commits do not change these frozen binary sources.

Wall and user times below are sums of complete scorr+stran pipeline times,
not concurrent batch makespans. Final counts use all 268 paired PASS cases.
SEQ metrics use the 261 paired profiled cases, with 6,410,945 input ANDs.
The other 7 cases have no remaining registers/profile after scorr and are
excluded from phase metrics, not assigned guessed zero profile fields.

| E5 flow | Wall s | User s | Final ANDs | Complete SEQ AND gain | Ordered SEQ Build AND gain |
|---|---:|---:|---:|---:|---:|
| Before stran | 7562.476 | 7530.049 | 4535123 | 20959 | 11058 |
| Before stran2 | 6552.052 | 6526.341 | 4522814 | 23424 | 13122 |
| Fixed stran | 7750.489 | 7715.844 | 4535306 | 20774 | 11105 |
| Fixed stran2 | 6737.674 | 6712.558 | 4522829 | 23406 | 13192 |

All groups finish with 363,418 registers; all 268 per-case register counts
are equal across groups. Total input ANDs/registers are 6,485,261/530,790.
Fixed stran reduces input ANDs by 1,949,955 (30.06749%); fixed stran2 by
1,962,432 (30.25988%). Both remove 167,372 registers (31.53262%).

### Fixed stran2 versus fixed stran

- Wall sum -13.06776%, per-case geometric-mean speedup 1.20504x (268 pairs).
  User sum -13.00293%, user geometric-mean speedup 1.17852x.
  Wall time improves on 220 cases and regresses on 48; this is one run per
  configuration, not a repeated-run confidence interval.
- Final ANDs improve by 12,477 (0.27511% of baseline final ANDs):
  90 better, 142 equal, 36 worse. Registers: 0 better, 268 equal, 0 worse.
- Complete SEQ gain +2,632 (+12.66968%); input-normalized gain
  0.324040% -> 0.365094%. Per-case: 81 better, 142 equal, 38 worse (261).
- Ordered SEQ Build gain +2,087 (+18.79334%); input-normalized gain
  0.173219% -> 0.205773%. Per-case: 80 better, 145 equal, 36 worse (261).
- SEQ proof-origin Build generated/proved/selected:
  11,742,415 / 31,085 / 3,712 -> 8,322,395 / 33,208 / 4,129.
  Actual SEQ-commit Build selections, including COMB-origin certificates,
  are 3,723 -> 4,142. These are distinct attribution dimensions.
- Largest wall saving: Problem05_label43+token_ring.03.cil-1, 142.703 s;
  largest regression: pc_sfifo_3.cil+token_ring.09.cil-2, 91.484 s.

### Search repairs versus before

These repairs restore valid tight-budget search paths; they are not a measured
speed optimization or a per-case QoR guarantee under finite scheduling.

- Stran2 wall sum +2.83304%, wall geometric-mean speedup 0.98955x.
  Final ANDs +15: 11 better, 252 equal, 5 worse. Complete SEQ gain -18
  (-0.07684%), ordered Build gain +70 (+0.53346%).
- Stran wall sum +2.48613%, wall geometric-mean speedup 0.99092x.
  Final ANDs +183: 16 better, 239 equal, 13 worse. Complete SEQ gain -185
  (-0.88268%), ordered Build gain +47 (+0.42503%).
- The aggregate small changes must not hide the fib_05 regression below.
  Keep this as an explicit review-fix branch; do not claim that it is a
  quality-preserving replacement for every production input.

## Closure accounting validation

The closure-only baseline exactly reproduces the archived merged-E5 final
AND/register counts and COMB/SEQ Build generated/proved counts on all 268
cases of each flow. This is a transformation-count invariance check, not an
equivalence proof. The archived complete SEQ boundary gains are reproduced.

All 261 profiled rows of every group have profile_accounting_complete=1.
The new parser rejects missing/duplicate records or a final-AIG boundary
mismatch. No failing assertion was disabled and no parse error became PASS.

| Fixed flow | Closure attempts | Closure selections | Closure AND gain | Closure CPU s |
|---|---:|---:|---:|---:|
| stran | 865 | 1230 | 2802 | 9.826070 |
| stran2 | 916 | 1212 | 2729 | 10.148988 |

Closure gain here is all kinds/phases combined, not exclusively Seq Build.
It is already included in phase totals; do not add it again. SEQ cleanup
gain beyond all selected marginal gains is 2,509/2,626 for fixed stran/stran2,
reported separately and not attributed wholesale to Build.

Old incomplete ordered Seq Build totals of 10,427/12,545 must be replaced
with the closure-complete before totals 11,058/13,122. This is a measurement
correction, not extra optimization obtained by printing more profile lines.

## Reproduced QoR regression: fib_05

Input:
/mnt/home/zhaoxiran/benchmark/all_test/all/bitlevel/safety/2024/hkust/arithmetic_circuits/fib_05/fib_05.aig

Under the full-matrix arguments, before gives 464 final ANDs and fixed gives
649, on both flows; registers remain 48. Complete SEQ gain falls 185 -> 0,
ordered Build gain 7 -> 0. A standalone fixed-stran2 rerun reproduces this
and passes DSEC against the normalized input.

The first immutable SEQ snapshot has 2,084 generated one-gate candidates in
both versions, but their proved count changes 5 -> 0. Total first-snapshot
Build generation is 2,244 -> 2,261, with div-gate 33 -> 66, gate-gate 21 -> 14,
and greedy 106 -> 97. Before commits and reaches four snapshots; fixed proves
no relation and stops after the first snapshot. Equal counts alone do not
prove identity of candidate lists or proof obligations.

Two bounded diagnostic reruns (one worker, 60 s per invocation, no DSEC)
changed one parameter at a time: C=10000 with q=10, and q=30 with C=1000.
Both still end at 649 ANDs. Neither changing production defaults nor a
proof/scheduling fallback was implemented. These results rule out those two
parameter changes as remedies, not every possible budget/search explanation.

Candidate-set changes affect shared proof batches and finite scheduling;
the specific lost obligations/helpers have not yet been identified. Do not
call this only prefix crowding, or label every split a real refutation.
The next diagnostic should match canonical candidate identities, first
proof divergence, SAT/UNKNOWN versus actual counterexample, and helper
retention before proposing a scheduling/proof-policy change to the user.

Small reproducer/equivalence artifacts are retained under
/mnt/home/zhaoxiran/script2/stran2_review_fixes/audit_20260905
(not in the raw batch archive). The cal103 and fib_05 fixed directories have
base.aig, final.aig, and dsec.log; fib_05 logs also preserve before/fixed and
the two diagnostic runs. Recheck a retained pair with the frozen fixed binary
using `-q 'dsec <absolute-base-path> <absolute-final-path>'`.

## Measured next priorities

Fixed stran2 has 5,938.990 s of recorded root-pass CPU time (not pipeline
wall time or the initial standalone scorr). Main buckets are:

| Bucket | CPU s | Share |
|---|---:|---:|
| Shared sequential proof, excluding SRM graph build | 2416.127 | 40.68% |
| Build discovery including divisor ranking and enumeration | 1939.243 | 32.65% |
| Root/frontier refresh | 886.874 | 14.93% |
| CBS | 439.768 | 7.40% |

BMC accounts for 1,610.748 s inside shared proof; do not add it to that parent
bucket. Frontier dynamic-gain computation accounts for 880.552 s. Closure
is only 10.149 s (0.17%) spread across these buckets, so it is important for
complete quality accounting but not the principal speed target.

1. Quality first: diagnose and resolve the fib_05 shared-proof sensitivity
   with canonical candidate/obligation evidence. Discuss the resulting
   algorithm change before editing proof policy, scheduling, or retention.
2. Semantics-preserving speed work: evaluate exact dynamic-gain reuse within
   an immutable snapshot, including repeated continuation pages (191.010 s
   of SEQ continuation frontier-loop work). Keys/invalidation must include
   graph and virtual selection state; generic changed-state callers still
   require fresh checks. Require candidate/order/proof/commit/output parity.
3. Build improvements after that: 62.79% of the measured SEQ enumeration
   zero/positive-root split is spent on zero-accepted roots. Diagnose causes
   instead of applying a new heuristic stop. E5 pool conflicts cover 45.65%
   of eligible root-visits; this does not prove infeasibility of a larger
   reservoir. Pool repair or DAG-aware cost changes need separate agreement.

Do not reduce Q/W/q/proof budgets to manufacture speed while the primary
goal remains high-quality sequential Build reduction. The full matrix is
complete for the historical 268-case survivor subset, not the 330-case
benchmark universe, and makes no equal-deadline timeout claim.
