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
