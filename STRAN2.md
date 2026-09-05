# &stran2: Current Goal And Results

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
