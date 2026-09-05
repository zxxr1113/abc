# Build exploration, 2026-09-05

Base: `ebe4efc92`, branch `codex/stran2-build-exploration`, isolated worktree
`/mnt/home/zhaoxiran/abc-stran2-explore`. The concurrent optimization task owns
the original `abc` worktree and its preprocessing/page-reuse changes.

## Experiment contract

The user authorized open algorithm experiments in a separate worktree. All
new behavior is opt-in through `-E`; zero retains the original search. Formal
CBS/scorr acceptance and commit are unchanged. Do not merge an experiment just
because its candidate count or proof rate improves.

Build with `TMPDIR=/dev/shm/stran2_explore make ABC_USE_NO_READLINE=1 -j48`.
The system `/tmp` filesystem has no headroom. Check CPU, live ABC processes,
memory and temporary filesystem space before every launch. Reserve 150 workers
for the concurrent task; this task uses at most 50 (including compilation).

Isolated runner/parser copies are in `/mnt/home/zhaoxiran/script2/stran2_explore`.
The other task's shared runner/parser are never edited. Full raw CSVs belong in
`/mnt/home/zhaoxiran/script2/experiment_reports/20260905_stran2_build_exploration`.
Smoke/pilot data and ordinary logs belong in `/dev/shm/stran2_explore`.

Fixed parameters: `-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -p`.
Pilot: first 32 sorted cases of the 268-case historical all-PASS corpus.
Full: all 268 cases, timeout 1800 seconds per invocation, DSEC skipped and
explicitly reported. This corpus has historical-survivor selection bias.
Small audit: built-in resub regression (including exact projection tests),
3 DSEC cases, and CI-subset shadow assertions on the combined path.

| E | Changed variable | Hypothesis |
|---|---|---|
| 0 | Baseline with timing instrumentation | Establish paired time/QoR |
| 1 | Exact TFI CI-count cache and lazy ties | Remove repeated CI traversal/membership work |
| 3 | E1 plus 1/16 root observation census | Quantify conflicts and repeated observations |
| 5 | E1 plus all-root exact selected-pool conflict check | Avoid searches with contradictory observations |
| 15 | E1/E2/E4 plus CI subset shadow | Small correctness audit only |

The runner supports `EXPERIMENT_SET=explore EXPLORE_MODES='0 1 3 5'`.
Use `MAX_PARALLEL=4 JOBS_PER_EXPERIMENT=12` for at most 48 workers.
Record the source commit, dirty status, binary/runner/parser SHA256 from CSV.

## Semantic checks

`q` bounds accepted Build candidates per snapshot in microbatch mode; `j`
bounds one proof page. One iterator `Next()` can internally consume multiple
failed Stage-5 pivots. Neither `q` nor the number of `Next()` calls is a
direct budget on search work.

Every divisor reservoir entry is collected from the root's combinational TFI.
Thus `CI(divisor)` is a subset of `CI(root)`, and their intersection size is
exactly `|CI(divisor)|`. Cache this count only for the immutable simulation
snapshot. Compute the original simulation score for every reservoir node;
compute CI counts for all top-B scores and the entire boundary tie group.
Retain each selected divisor's original overlap metadata, including when its
primary score was unique. This preserves tie-breaking and candidate ordering.

Observation keys contain every divisor bit (up to 64 physical divisors).
Open-addressing hashes only locate entries; full keys are compared exactly.
If one key occurs with both root labels, no function of that fixed pool can
satisfy the observations. The source is simulated before projection, and all
nodes use the same observation positions. No induction CEX is introduced.
For >64 divisors, the checker reports unmeasured and never prunes.

The diagnostic measures the full collected reservoir separately from the
selected Build pool. Neither is the unrestricted set of every legal divisor
in the graph. A pool contradiction is not a global circuit impossibility
claim. E4 marks the configured Build universe exhausted using this exact
certificate; `exp-pruned` distinguishes it from iterator exhaustion. Direct
discovery still runs. No-conflict is not proof of existence or of a feasible
recipe under the gate budget.

`exp-obs-unique` counts distinct `(D, root)` rows, including both labels on a
conflicting key. Duplicates can be removed without changing consistency, but
their multiplicities affect the current popcount-based ranking. Consequently
observation compaction would preserve constraints, not necessarily iterator
order, candidate horizon or final QoR. It is only measured in this iteration.

`exp-zero-build-sec` and `exp-positive-build-sec` attribute all per-root Build
calls to the final accepted count on that snapshot. Ranking is separately
attributed for Build-eligible roots; MFFC=1 ranking is excluded from those two
buckets. Observations are sampled by a fixed root-ID hash when E2 is set;
these are root/snapshot samples, not independent statistical circuit samples.

## Evaluation

Check statuses first. Pair by relative input filename with both pipeline
stages PASS and no equivalence failure. Report wall/user totals and geometric
mean speedup, final AND/latches, per-case better/equal/worse, generated/proved/
selected, Build and ranking time, total sequential gain and ordered Seq Build
gain normalized by input AND. Timing is subject to shared-host noise.

E1 must preserve all output/gain/candidate counts. E5 is expected to preserve
accepted candidates and QoR but intentionally changes iterator-work counters.
Reject E5 if its checking overhead outweighs the avoided search.
