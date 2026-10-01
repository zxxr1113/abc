# Fixed image-domain counterexample diagnostic

`diagnostic.py` is a separate mechanism diagnostic. It changes neither production ABC nor
`nonlinear_divisors/prototype.py` or `anytime.py`, and does not itself produce area
results or run DSEC. The separate `audit_products.py` reconstructs and verifies
products and bounded Direct sensitivities at separately recorded extra cost.
Neither script claims native recipe novelty.

## Domain and hypothesis

The standalone candidate class already requires both `D(0,x)=0` and
`D(T(s,u),x)=0`, with arbitrary and independent previous state `s`, previous PI
`u`, and current PI `x`. A SAT witness for the latter is therefore a legitimate
hard sample for this fixed image-valid search class. It is **not** a reachable
reset trajectory, and must not be fed to a general reachable-state teacher or a
weaker/deeper image proof lane. For example, `q'=q`, reset zero, admits the
reachable relation `q=0` while unrestricted-image samples can refute it.

The falsifiable hypothesis is that random signatures miss rare image-domain
mismatches, letting false high-gain recipes monopolize the top eight slots.
Adding independently replayed countermodels should reduce signature matches and
expose image-valid lower-ranked recipes with the *same roots, pools, recipes,
free samples, costs, and final proof class*. Matched-random observations test
whether SAT direction matters rather than merely adding lanes.

## Frozen protocol

`protocol.json` fixes the first recorded 32-root chunk for mem_ctrl, wb_dma,
b20_opt, and des_area. Empty chunks remain empty. Each case has a 120-second
cooperative diagnostic deadline; all completed runs report total elapsed time.
This is extra research cost, not an equal-transform-budget quality comparison.

1. Verify frozen dependency and solver hashes, reconstruct the entire source
   proof CNF and literal map byte-for-byte, and bind every saved status to its
   raw query/result receipt. Reproduce original search candidate identities and
   discovery counters with the exact saved pool.
2. A separate C helper repeats only saved image-SAT queries, with the original
   1,000-conflict cap, and returns all requested graph PI values for SAT only.
   UNKNOWN never generates a sample. Graph-source variables have explicit
   roles and disjoint previous-PI, previous-state, current-PI identities.
3. Validate the source miter, then independently simulate the original AIG
   transition and original-ID recipe. Replayed witnesses retain input/source
   hashes, exact query/candidate identity, domain, and frame assignments.
4. Deduplicate exact `(current PI, successor state)` assignments. Append these
   image observations to the existing reset+image signature domain, leaving the
   free-state witness domain unchanged. Per-root ordered `(root, pool...)`
   projection novelty/duplicates are reported separately; no root-only or
   frequency-based compression is used.
5. Rerun the same roots/pools and compare a control with the same number of
   unique randomly generated image assignments (fixed seed 2026100207).
6. Newly retained candidates from either arm receive the original independent
   free witness replay and free-SAT/reset-UNSAT/image-UNSAT queries. Samples
   never confer proof or commit authority.

No mutable search or SAT cache persists between these reruns. The source graph
is immutable and all semantic search state is reconstructed. A future online
lane would need sample-versioned alias/ranking/iterator state, a new-constraint
progress condition even when no area improves, and the existing hard total
transform budget. That integration is implemented separately in `../nonlinear_divisors/image_guided.py`
and the opt-in anytime runner; it is not part of this diagnostic command.

## Commands

Use an already-built `libabc.a`; the helper build deliberately does not invoke
`make` or alter the existing query solver:

```sh
bash research/stran2-guide-20261002/image_cegar_diagnostic/build_model_solver.sh \
  /tmp/stran2-image-model-solver
STRAN2_MODEL_SOLVER=/tmp/stran2-image-model-solver python3 -B -m unittest discover \
  -s research/stran2-guide-20261002/image_cegar_diagnostic -p 'test_diagnostic.py' -v
python3 -B research/stran2-guide-20261002/image_cegar_diagnostic/diagnostic.py \
  --run /tmp/nonlinear-anytime-pilot-v1 --out /tmp/image-cegar-diagnostic-user \
  --model-solver /tmp/stran2-image-model-solver --solver /tmp/stran2-query-solver
```

The output directory must not exist. `--run` names a complete frozen anytime
run with its own source directory, plan, raw chunks, and integrity report.
Output records include every empty/failed/timed-out case. An error or timeout
is not interpreted as a zero opportunity or a proof.

## First mechanism result

The first completed diagnostic is `/tmp/image-cegar-diagnostic-v1` on this
host. Exact source snapshots and hashes are in that result directory.

| Case | SAT models / unique image samples | Positive sampled recipes: control / directed / random | New fully certified candidates: directed / random |
|---|---:|---:|---:|
| mem_ctrl | 232 / 14 | 819,778 / 48,516 / 819,778 | 49 / 0 |
| wb_dma | 173 / 28 | 7,753 / 635 / 7,752 | 9 / 0 |
| b20_opt | 0 / 0 | 0 / 0 / 0 | 0 / 0 |
| des_area | 15 / 7 | 1,982 / 1,617 / 1,982 | 0 / 0 |

All source candidate identities and discovery counters reproduced. All 420 SAT
models replayed; none was UNKNOWN. The directed arm refuted all 232 old
mem_ctrl candidates and all 173 failed wb_dma candidates while retaining all
four previously proved wb_dma candidates. mem_ctrl exposed 49 new certified
recipes across 12 roots; wb_dma exposed nine across seven roots.

Total diagnostic elapsed times were 51.90, 2.65, 1.12, and 1.53 seconds,
respectively, including control and random reruns and source validation.
mem_ctrl discovery was 23.59 / 1.53 / 22.42 seconds for control / directed /
random. These are observational single-run costs, not a production speedup.
The directed model extraction/replay stages were 2.23, 0.85, 0.23, and 0.30
seconds; source construction/validation and other overhead remain included in
the total elapsed times. Total new-candidate proof work was 750 queries.

This supports top-k contamination and sample-directed discovery as a mechanism
on two independent designs. It does not yet establish exact selected-set area,
benefit after conflict selection, same-budget scalability, or native novelty.
The b20 empty chunk says nothing about later b20 roots; des_area's negative
result remains a real limitation. Keep the next step bounded and separately
audited rather than treating candidate counts as achieved Build area.
