# &stran2: Current Goal And Results

## Merge candidate: targeted signature guidance (2026-09-12)

The user requested a merge-ready improvement to the existing single-root
constructor. Source commit: `f4fbe6631`; separate cursor cleanup: `02f788aee`. The review branch is `codex/stran2-signature-guide`, based on
`3836f6091079664641bf42764b8a03c2310f6b54`. Production `codex/stran2` and its
unrelated working-tree edits were preserved. This entry documents an optional
candidate; the approved baseline below remains the production default.

The implementation strengthens the observation table supplied to native
core/Build construction. The constructor still builds a recipe for one root,
and the existing boundary proof, composition check, insertion and exact gain
check decide whether it can replace that root. It adds no rewrite pass,
multi-output synthesis, new divisor family, or SAT-generated recipe.

### Algorithm and correctness contract

1. At each immutable ODC discovery snapshot, evaluate one deterministic word
   (64 assignments) with free combinational inputs: PIs and register outputs.
   This costs one graph traversal shared by all roots and uses a separate RNG.
2. If a root has only one target value under the original observation care,
   append its and the complete divisor pool's auxiliary columns. In H2, if
   this word is also constant, ask bounded SAT for the opposite root value
   missing from that auxiliary word.
   SAT assigns input values only. There are at most 64 queries per snapshot,
   each capped at 100 conflicts. A satisfying partial assignment is completed
   into 64 concrete lanes; only the root/pool union cone is evaluated.
3. Preserve every original care observation. Compact the joined rows only
   when the full divisor vector **and target label** are equal. Opposite
   labels for the same pool assignment remain a conflict and stop this
   impossible construction attempt. Feed the resulting table to the existing
   constructor with its original pool, ranks, q and construction families.
4. Every candidate still requires the existing formal boundary obligations
   and composition/commit checks. Auxiliary samples confer no proof status.
   SAT UNSAT/UNKNOWN here neither proves a replacement nor adds a sample.

Free register-output assignments are **not reachable sequential CEX**. They
strengthen the construction constraints and can exclude legal sequential/ODC
recipes. H3 also triggers when a sampled root/divisor equality or complement
is disproved by the auxiliary word; it is an experimental quality tradeoff.
None of these modes guarantees per-circuit monotonic improvement. This does
not complete the research on reachable, observability-aware CEX teaching.
It also does not establish completeness of the native constructor relative
to exact SAT synthesis: missing divisors, restricted recipe families and
budget/selection gaps remain separate possible causes of lost opportunities.

The integration replaces the prototype's global scratch context and fixed
joined-buffer size with per-snapshot ownership and dynamic capacity. A private
SAT AIG with an explicit literal map leaves source `Value` fields untouched;
CI ordering, buffers and native XORs are handled explicitly. Cone evaluation
uses an iterative stack. The profile includes early-return checks, preparation,
SAT outcomes and compression counts; SAT seconds are nested within guide
seconds and must not be added twice.

An independent memory check also exposed an existing ODC cursor leak with H0:
only caches were freed, leaving the frozen pool and ranks allocated each round.
The branch uses the existing complete cursor destructor at the same cleanup
point. This is a separate resource-lifetime repair, with no algorithm change.

### Reproduction

Build with assertions enabled, e.g. `make -j16 ABC_USE_NO_READLINE=1` on this host.
From a fresh result directory, run:

```sh
ABC=/mnt/home/zhaoxiran/abc-signature-guide/abc \
AIG_DIR=/path/to/inputs TMPDIR=/path/to/existing/scratch \
TIMEOUT=1800 MAX_PARALLEL=2 JOBS_PER_EXPERIMENT=8 \
SKIP_DSEC=0 KEEP_ARTIFACTS=1 \
bash /mnt/home/zhaoxiran/abc-signature-guide/scripts/run_stran2_signature.sh
```

`SIGNATURE_GUIDE_MODE=0/1/2/3` selects the arm; the new preset defaults to H2.
The bare command defaults to H0 and `run_stran2_quality.sh` is unchanged.
Direct `-H` usage requires care-aware `-k -J` construction, spatial windows,
`ABC_CEX_MODE=2` and `ABC_CEX_COMPRESS=4`; incompatible combinations are rejected.
The preset holds the approved baseline's Q4/W8, long Q1/W256 observations,
B128/q320 ODC budget, D4 windows and L16 cap fixed. It runs both common flows.

### Fresh final-binary fast35 results

All 35 original input hashes are paired, with both `scorr-stran` and integrated
`stran2`, all four modes, 1800 seconds per invocation and 64 maximum workers
per matrix. All 280 final-binary rows are execution/parser/DSEC PASS; there
are no timeouts, assertions, profile errors or excluded cases. Latch sum is
1,776 in each arm. Quality agrees across the two flows and every final graph
(excluding names/comments) matches the corresponding frozen research prototype.

The following is **integrated `stran2`**. Reduction is the arithmetic mean of
per-circuit gain divided by normalized source ANDs; Build means
`seq_build_ordered_and_gain`, total SEQ means `seq_stage_and_gain`. Runtime is
the arithmetic mean / median of per-circuit pipeline-time ratios against H0,
including initial scorr and excluding normalization and independent DSEC.

| Mode | Ordered Build/source | Total SEQ/source | Final AND sum | Better/equal/worse vs H0 | Runtime mean / median ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| H0: Control | 6.711162% | 7.254798% | 18,697 | 0/35/0 | 1.0000 / 1.0000 |
| H1: One auxiliary word | 8.868207% | 9.411842% | 17,806 | 14/21/0 | 0.9176 / 0.9767 |
| H2: Recommended: word + missing-value SAT | 9.013059% | 9.556694% | 17,709 | 14/21/0 | 0.9218 / 0.9851 |
| H3: Also break observed aliases | 9.072764% | 9.616399% | 17,689 | 14/18/3 | 0.8488 / 0.9821 |

Recommended H2 removes 988 additional ANDs in aggregate,
with 14 circuits better, 21 equal and 0 worse.
Its mean runtime change is -7.82%, with median
-1.49%. These are fixed-seed observations on a
selected fast35 corpus, not a generalization or statistical speed guarantee.
Some individual runtimes increase; sub-second cases are sensitive to launch
and scheduling variation. The complete per-case data are retained.
H3 has three known one-AND regressions (b09, b09_opt, b11_opt), which is why
it is not the recommended preset despite its better aggregate reduction.

The H2 ODC phase generates 899,020 candidates versus
1,904,077 for H0, proves
14,823 versus
9,487, and selects
966 versus 658.
ODC proof time totals 528.725s versus
776.047s. H2 guide preparation totals
0.001330s, guide work 0.135382s,
including SAT solving 0.002945s. The interpretation is that
more informative signatures avoid many unproductive recipes and expose more
useful native constructions. At the fixed q/W budget, targeted assignments
supply distinctions missing from the original observation table. Legacy `seq_constructed_*` counters omit this ODC phase
and must not be used as its candidate totals.

### Validation and evidence

- Clean full build and the final cursor-fix rebuild; assertions enabled.
  Native `&stran_resub_test`, 21 combined signature/closure/report Python tests,
  and the 11 profile tests pass. New native tests cover a 513-word input table,
  exact truth-row preservation, contradictory labels, bounded rare-value SAT,
  UNSAT/UNKNOWN, CI mapping and untouched source scratch fields.
- Final binary focused USB H0/H1/H2/H3 and i2c H2: 5/5 independent DSEC PASS.
  Final AddressSanitizer selftest and USB H0/H2 plus i2c H2 runs pass, with
  leak detection enabled and independent DSEC for all three final products.
  Instrumentation covers the changed C translation units; unchanged dependencies
  come from the clean build. Pre-fix leak reports are retained.
- Five additional quick-corpus circuits selected by header structure and
  SHA1(relative path), without constraints/justice/fairness, are tested in
  H0/H2 and both flows: 20/20 execution and independent DSEC PASS. All bad-state
  predicates are retained as observed POs. Existing ABC initialization
  normalization adds PI/mux/phase state for uninitialized registers, which is
  audited explicitly. H2 improves three integrated results and ties two;
  this small sample is regression coverage, not a broad corpus claim.
- The first hardened full matrix, before the cursor lifetime repair, also has
  280/280 PASS rows. The final matrix is the release result above; the earlier
  matrix is retained as separate provenance, not mixed into timing averages.

Final binary SHA256: `b065ca44164f42f5460fdd2bc1943138b6c5faa4ffe2f97d4c822ee9e1b64def`.
Complete release raw CSV pairs are under
[`20260912_signature_guide_release_h2/`](/mnt/home/zhaoxiran/script2/experiment_reports/20260912_signature_guide_release_h2)
and corresponding `h0`, `h1`, `h3` directories. Build/source hashes, command
settings, all logs, graphs, independent audits, prototype comparison, profile
analysis and the scoped patch are archived in
[`signature_guide_merge/20260912/`](/mnt/home/zhaoxiran/script2/evidence/signature_guide_merge/20260912).

## Approved development baseline: TFO + complete-information ODC (2026-09-10)

The user selected the **6.7111623876%** fast35 Ordered Seq Build/source
configuration as the next production development baseline and asked to pause
further algorithm exploration for technical discussion. This entry supersedes
the historical sections below when they describe an older "current" baseline.

The selected source is `bed995558b0a44d4dc6455a2056bce8ea658c447`, merged into
`codex/stran2` while retaining its `9be377928` frontier reference-scratch repair.
TFO is already part of this selected source. The integration includes its ODC
window/boundary proof and batch-commit dependencies, complete reachable
observation quotient before native core/Build search, and exact bidirectional
bit transposition. It stops before the subsequent core-reuse, witness,
minimum-support SAT, and local-realization-value experimental commits.

The reproducible baseline entry is
[`scripts/run_stran2_quality.sh`](/mnt/home/zhaoxiran/abc/scripts/run_stran2_quality.sh).
Run it from a fresh result directory, setting `ABC`, `AIG_DIR`, and an existing
`TMPDIR` as needed. It calls the common paired runner with fixed algorithm
settings; `TIMEOUT`, `LIMIT`, worker counts, `SKIP_DSEC`, and `KEEP_ARTIFACTS`
remain runner controls. The generic runner and bare ABC command defaults are
not the baseline preset.

- Strict prefix: B16/q20, Q4/W8, Kit/BDC, F1/C1000, TFO enabled.
- Additional ODC: B128/q320/L16, spatial D4, existing alternate care cores,
  full divisor pool, CBS plus sequential boundary proof, no extra ODC Direct.
- `ABC_CEX_MODE=2 ABC_CEX_COMPRESS=4 ABC_CEX_PACK_FAST=2`, projection toggle 0.
  Long Q1/W256 observations are simulated once per immutable snapshot; rows
  are merged only on equal target and complete pool values under care.
- "Complete information" means the complete supplied observation matrix,
  not exhaustive reachable-state coverage. Observations guide construction;
  formal candidate/bundle proof requirements remain in force.

Frozen reference and fresh merged full fast35 result: both flows 35/35 execution/parser PASS,
Build/source mean 6.7111623876%, total SEQ/source mean 7.2547975419%, final
AND sum 18,697, latches 1,776. This is a fixed-seed selected fast corpus,
not a full58/quick268 or statistical generalization result.

Merge validation is complete; the result and exact source/binary
identities are recorded under
[`integration/`](/mnt/home/zhaoxiran/script2/evidence/cex_reconstruction/20260910/integration).
The source builds with assertions enabled; `&stran_resub_test` and all 11
committed-parser tests pass. All 70 final graphs (excluding symbols/comments),
per-case quality fields, and per-round ODC counts match the frozen reference.
The committed parser also reproduces the quality/accounting fields of all
70 logs independently of unrelated working-tree parser additions. There were
no execution, timeout, assertion, or profile failures in the full matrix.
Eight selective final-network DSEC checks pass: b03/b04 focused and b05/des_area
full results, each in both flows, after consistent positional port naming.
The full matrix explicitly skips DSEC; these are selective formal audits.
Complete raw CSVs are in
[`20260910_cex_quality_mainline/`](/mnt/home/zhaoxiran/script2/experiment_reports/20260910_cex_quality_mainline).
Existing unrelated working-tree edits are preserved.
Build command on this host: `make -j16 ABC_READLINE_LIBRARIES=-l:libreadline.so.8`
(the installed readline library has a versioned filename).

Updated 2026-09-05. One development tree: `/mnt/home/zhaoxiran/abc`,
branch `codex/stran2`. Goal: preserve high-quality total SEQ and ordered
Seq Build reduction while reducing runtime. First unresolved task: the
fib_05 proof-context/UNKNOWN quality regression. No proof-policy fix yet.

## Tested Configuration

Algorithm: E5 + immutable-page reuse + Stage-3/Stage-5 review repairs +
closure-complete profiling. Cleanup changes tools/docs only, not `src/`.
Tested source: `45a89cbdb9644b62c923bf5d58890c15dc05f5c6`;
later documentation base: `aa163f7e132533539eba6b867d93fbf78717bfa6`.
Tested binary SHA256:
`e7e3a9c6bedc623a6cd3fe0cbfd10728a1ac401b75f98fd767f069a39ae7d7b5`.

Both flows use `-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -E 5 -p`.
Compare default `&scorr; &stran` with integrated `&stran2`, which runs its
own default scorr and retains reachable CEX as teaching trace lanes.

Raw evidence: `/mnt/home/zhaoxiran/script2/experiment_reports/20260905_stran2_review_fixes/`.
Current pair: `stran_fixed_stran_E5_Q4_W8_q10.csv` and
`stran_fixed_stran2_E5_Q4_W8_q10.csv`; before-fix pair also retained.
All four groups: 268 matching input hashes, 1,072 execution PASS rows,
zero timeouts/assertions/ABC/profile errors or missing/malformed rows.
DSEC SKIP=1,072, not a full equivalence audit. Separate fixed-output DSEC
audits passed on cal103 and fib_05. Additional diagnosis retained three
distinct DSEC pairs and one PDR property, all passed.
This is a historically all-PASS selected corpus, not the full 330-case set;
one observation per configuration, with shared-host noise. Timeout was
1800 s per invocation, not a common end-to-end deadline.

## Runtime: Equal Weight Per Circuit

The user's requested approximation is
`R2 = mean_i(T(stran2)_i / T(scorr)_i - 1)`.
Use the paired standalone scorr measurement, not the integrated CSV's zero
placeholder. For standalone stran, `R1 = mean_i(T(stran)_i / T(scorr)_i)`.
These are means of individual ratios, NOT ratios of summed times.

| 268 paired circuits | Standalone stran | Stran2, initial scorr approximately removed |
|---|---:|---:|
| Arithmetic mean wall-time multiple of scorr | 17.5406x | 15.5316x |
| Median wall-time multiple | 10.0671x | 8.2091x |
| Arithmetic mean user-time multiple | 18.9485x | 16.9212x |
| Mean extra wall seconds per circuit | 26.0105 | 22.2314 |

Stran2's mean relative wall overhead is 2.0090 scorr units lower. This is
not a claim that every case speeds up by that amount. Four wall estimates
are slightly/meaningfully negative because separate short runs differ;
retain them without clipping under the requested approximation. Do not
interpret them as negative physical work or compute a geometric mean of
these net estimates. The median provides a less tail-sensitive companion.

## Reduction And Quality

| Metric | Default scorr | Scorr + stran | Stran2 |
|---|---:|---:|---:|
| Final ANDs, 268 circuits | 4,585,633 | 4,535,306 | 4,522,829 |
| Extra ANDs removed after scorr | 0 | 50,327 | 62,804 |
| Extra reduction / scorr ANDs | 0 | 1.09749% | 1.36958% |
| Final latches | 363,418 | 363,418 | 363,418 |
| Total SEQ AND gain, 261 profiled circuits | n/a | 20,774 | 23,406 |
| Ordered Seq Build AND gain, same 261 | n/a | 11,105 | 13,192 |
| Total SEQ gain / input ANDs, same 261 | n/a | 0.324040% | 0.365094% |
| Ordered Seq Build gain / input ANDs, same 261 | n/a | 0.173219% | 0.205773% |

All-input totals: 6,485,261 ANDs and 530,790 latches. Profiled input ANDs:
6,410,945. Seven inputs reduce to zero AND/latches at scorr and have no
root profile; no missing profile fields were imputed. Their paired scorr
and final counts are explicitly measured as zero.

Stran2's 62,804 extra AND reduction consists of COMB 39,398 + SEQ 23,406.
Ordered Seq Build contributes 13,192, 56.36% of SEQ and 21.01% of all extra
reduction; it is a subset, not a quantity to add to total SEQ again.
Compared with scorr: 199 better / 69 equal / 0 worse final AND results.
Compared with stran: 90 better / 142 equal / 36 worse; 12,477 extra ANDs
removed overall. Total SEQ gain +12.67%; ordered Seq Build gain +18.79%.
No additional latch reduction beyond scorr in this matrix.

SEQ proof-origin Build generated/proved/selected:
stran 11,742,415 / 31,085 / 3,712; stran2 8,322,395 / 33,208 / 4,129.
Actual SEQ-commit Build selections are 3,723 / 4,142 respectively;
proof origin and commit phase are different attribution dimensions.

## What Was Kept

- E5 = exact TFI CI-count reuse/lazy ties plus an exact contradiction check
  on the selected divisor pool. Equal divisor observations with opposite
  target bits mean no function of that pool can fit the observations, so
  Build can skip the impossible search. Direct and proof remain enabled.
  This is not a claim that the full reservoir or entire circuit is infeasible.
- Earlier full E0/E5 comparison preserved all per-case final AND/latch counts
  and the measured Build generated/proved/selected counts. Its mean per-case
  extra wall multiple fell 39.07x -> 15.58x using one common scorr reference.
  Those are historical pre-review measurements, not the current 15.53x run.
  E1 alone removed repeated CI work; E3 added observation diagnostics, not
  another quality improvement. E5 includes E1. Other speculative branches
  remain archived; incompatible algorithms were not merged indiscriminately.
- Review fixes restore the asymmetric Stage-3 literal+pair coverage bound
  and Stage-5 one-gate residual leaf with the pending-alternate constraint.
  Stage 5 is not the same thing as command option `-E 5`.
- Closure drains profitable already-proved certificates through further
  non-overlapping commits without regenerating or reproving candidates.
  It already existed; schema 8 repaired accounting, including actual commit
  phase, cleanup attribution, complete boundaries and final AIG checks.
  Stran2 closure: 916 attempts, 1,212 selections, 2,729 AND gain across all
  kinds/phases, already included above. It is not exclusively Seq Build.

## Bottlenecks And Next Decision

Mean of each circuit's stage/profile-time fractions on the 261 profiled
stran2 cases: Build discovery 70.97%, shared sequential proof 14.94%,
root/frontier refresh 6.19%, CBS 3.12%, closure 0.22%.
These are equal-circuit averages, not time-weighted fractions. On this Linux
build Abc_Clock uses CLOCK_MONOTONIC: profile values are elapsed time, not
user CPU; they exclude initial scorr but do not cover all command overhead.
Build remains the broad target; proof and dynamic-gain refresh matter on
expensive outliers. Closure is not a major runtime target.

1. Quality first: fib_05 gives 464 AND before review fixes versus 649 after;
   SEQ gain 185 -> 0, ordered Build 7 -> 0. All five previously proved Build
   relations in the initial snapshot were generated and submitted unchanged,
   but no longer proved. This is not commit dropping identical proved inputs.
   Raw first-SEQ UNKNOWN counts are old=10/new=6 at C1000. Even C=10,000,000
   leaves one conflict-limited UNKNOWN: batch 2, round 14, output 138,
   ring edge 323 -> 150. Later valid relations split during resimulation.
   Earlier UNKNOWN may be an indirect cause; it has NOT been ruled out.
   Next: capture/audit that exact SRM obligation and replay its causal effect
   before changing proof policy. F2 restores total SEQ but Build remains zero.
2. cal103 q10/q15 preserves the old candidate/proof prefix, not the whole
   proved pool. The extra page changes selection; a better first result
   ends 34 AND worse under w8. It is a separate finite-budget path issue.
3. After diagnosis, discuss bounded proof rescue/context retention versus
   cost. Independently prioritize exact reuse and lossless Build pruning;
   do not buy speed by globally shrinking q/Q/W or accepting unproved nodes.

Evidence: `/mnt/home/zhaoxiran/script2/evidence/{quality_stability,review_fixes,gain_bug_fix}`.
Diagnostic tracer source `c2784e32a` (before tracer `29723f085`) is in the
Git recovery bundle, not enabled in the production binary. Its historical
source/probe details remain in `doc/stran_quality_stability.md` at that commit.

## Reproduce And Maintain

One tool copy lives in `abc/scripts`; `script2` contains symlinks, full raw
CSVs and necessary evidence. Run `run_bench_parallel.sh` from a new dated
report directory after resource preflight. Use a temporary directory for a
LIMIT smoke, and remove it afterward. No fresh full batch was needed for
cleanup: source/binary identity was preserved. Cleanup verification passed
both built-in self-test lines, 12 Python tests and one case in both flows.

```bash
R=/mnt/home/zhaoxiran/script2/experiment_reports/20260905_stran2_review_fixes
python3 /mnt/home/zhaoxiran/script2/analyze_stran2_report.py \
  "$R/stran_fixed_stran_E5_Q4_W8_q10.csv" \
  "$R/stran_fixed_stran2_E5_Q4_W8_q10.csv" --relative-scorr --per-case
```

Recovery archive: `/mnt/home/zhaoxiran/archive/stran2-pre-cleanup-20260905`.
It contains all old Git refs/history, the pre-cleanup script2 tree and
workflow, and the tested binary. Old local branches/worktrees were removed;
remote refs and benchmark inputs were not changed. Keep this one current
report; update its baseline and next decision rather than adding handoffs.
