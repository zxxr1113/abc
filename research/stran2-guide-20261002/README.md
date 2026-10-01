# STRAN2 Guide research snapshot

Read [STRAN2.md](../../STRAN2.md) first. It is the authoritative goal, baseline, result, and workflow record. This branch is a frozen, paused research snapshot; it is not a production integration.

The primary metric is exact non-combinational SEQ Build AND reduction after the fixed strong `scorr` plus matched COM prefix, divided by each case's original ABC-loaded AND and then averaged equally across paired valid cases. A candidate needs a free PI/RO SAT witness, complete sequential proof, positive exact selected-set cleanup gain, and independent DSEC before it counts. The 55 frozen New58 inputs and their loaded baselines are in `inputs/`; `cases.json` lists hashes and sizes. Three other New58 cases had no verified fixed prefix and remain excluded, as recorded in `STRAN2.md`.

The saved experiment sources are in `seq_cut_image/` and `seq_care_aig3_completion/`. The exact isolated runtime ABC source is `seq_cut_image_runtime/builds/20261001T162338Z_shuguang_554899/seq_cut_image_runtime.source.tar.gz`; it passed the required build checks but was stopped before smoke or the five-arm area matrix. Its higher-order clause extension is also shown in `seq_cut_image_runtime/source.patch`. The original production ABC algorithm was unchanged.

`seq_cut_image/final_results.json`, `seq_care_aig3_completion/interaction/final_results.json`, and `new58_unified/all58_case_metrics.csv` are compact batch results. `mem_ctrl_independent_review/review.json` records the independent review of the older 814-AND result. These saved JSON files contain historical absolute evidence paths; the full raw solver logs and final product graphs remain on the original research host and are not in this Git package. The packaged result summaries are useful for choosing the next mechanism, not a replacement for replaying proof and DSEC on a new host.

To rerun one pair/full-cut offline construction case on the packaged first-SEQ graph:

```sh
bash research/stran2-guide-20261002/build_query_solver.sh /tmp/stran2-query-solver
python3 research/stran2-guide-20261002/run_cut_image.py \
  --case 034_b20_opt.aig --mode full \
  --solver /tmp/stran2-query-solver --out /tmp/stran2-b20opt-full
```

The diagnostic retains the original K6/CAP8, greedy SOP, and SAT query rules. The historical batch runner applied a 120-second wall limit to each case; the single-case wrapper above does not impose that limit. Run a uniform frozen cohort with the same limit and keep timeouts as missing data. The completed mechanism diagnosis points toward reusing existing nonlinear divisors or changing the input basis; merely extending the current cut-leaf completion did not produce broad large-case gains. The workflow now stops expensive full-product matrices when a short batch shows only isolated improvements.
