# Isolated &stran2 review-fix workspace

This worktree is owned by the review task. The user authorized fixes for
closure profiling, asymmetric Stage-3 coverage pruning, and the Stage-5
one-gate residual base case, followed by complete comparison experiments.
Use `/mnt/home/zhaoxiran/abc-stran2-review-fixes` on
`codex/stran2-review-fixes` for edits/builds; the continuation-path and
read-only-first-turn restrictions below are historical and superseded here.
The newly created detached `/mnt/home/zhaoxiran/abc-stran2-review-before`
is the closure-only baseline; its unchanged source may be built for the
paired experiment. Do not edit or rebuild any pre-existing worktree.
Use isolated scripts under
`/mnt/home/zhaoxiran/script2/stran2_review_fixes` for this experiment.

Read `/mnt/home/zhaoxiran/AGENTS.md` completely, then read
`/mnt/home/zhaoxiran/script2/WORKSPACE_INDEX.md` and
`/mnt/home/zhaoxiran/script2/NEXT_SESSION_PROMPT.md` before task actions.

This worktree was created for the user's new-session handoff on 2026-09-05.
Its algorithm source base is `7ab7b574cb393349038d06b976887319fe484650`.
The initial handoff commit changes instructions only, not the algorithm.

## Isolation overrides

- Use `/mnt/home/zhaoxiran/abc-stran2-next` and branch `codex/stran2-next`
  for subsequent source edits/builds; do not use the parent instructions'
  historical `/mnt/home/zhaoxiran/abc` build path for new changes.
- Protect task `01a066e8-12cd-74d1-9760-e3464f3b5694`: do not switch its
  checkout, replace its binary, move its outputs, stop its jobs, or message
  it with instructions without a new user request.
- Also protect `/mnt/home/zhaoxiran/abc-stran2-explore`,
  `/mnt/home/zhaoxiran/script2/stran2_explore`, its reports, and its jobs.
- Preserve the detached before/after experiment worktrees and binaries.
  They are frozen inputs to an existing batch, not new development folders.
- Do not merge/cherry-pick the exploration branch without discussing it.
- Shared `script2` runners/parsers are read-only during the handoff. Reuse
  them for analysis; coordinate changes before other tasks' next launches.
- First continuation is read-only status/analysis. Do not duplicate batches,
  rebuild, change ranking, or start new tests just because this is a new task.
- Existing main batch has a 150-worker cap; the other 50-worker allowance is
  reserved for the user's separate exploration. Check all live runs before
  adding workers; a new window does not create another 150-worker allowance.

## Documentation caveats

`doc/stran2_teaching_signatures.md` describes an older algorithm. In
particular, its eight-word/16-CEX policy and bundle wording are not the
current implementation. Consult `cecTrans.c`, current CLI help, and the
workspace index. Do not silently change the algorithm to match an old doc.

Permanent reports contain only complete full-batch raw CSVs from the normal
runner. An actively written CSV/atomic `.tmp` is not a completed report and
must not be deleted or moved. Keep handoff notes outside `experiment_reports`.
