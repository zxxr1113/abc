# Fixed free-domain witness diagnostic

This is a separately timed research diagnostic, not production or online integration.
`../../../STRAN2.md` remains the project report. See `protocol.json`, `summary.json`,
and `validation.json` for the frozen boundary and compact evidence.

## Result

The fixed four-case first-32-root experiment completed in
17.25 / 3.73 / 2.71 / 3.43 seconds (mem_ctrl / wb_dma / b20_opt / des_area),
including preparation, arm searches, fresh proofs, and independent full-world
and witness replay. Every initial arm reproduced the exact saved first-image-
refinement search identities, costs, witness lanes, and aggregate counters.

- mem_ctrl: 232 pre-successor-dedup models yield 14 distinct added worlds in
  each predecessor-PI and current-PI arm. Both retain the same 19 newly
  witnessed identities; three at root1263 pass free SAT/reset0 UNSAT/image
  UNSAT. One old proved identity is displaced from top-k: 49 initial proved
  candidates becomes 48 retained old plus 3 new, not 49 plus 3
- wb_dma: 173 models yield 24 predecessor-PI and 25 current-PI worlds. Both
  expose the same one new retained identity, which fails image proof
- b20_opt: the originally empty first chunk stays empty. All zero-addition
  arms transparently reuse the identical-domain initial search
- des_area: 15 models yield seven added worlds in each arm. No new retained
  identity. The current-PI arm reduces no-witness rejections by 36, but all
  newly witnessed recipes fail positive cost; this illustrates why early
  funnel counters are not missed-Build counts
- Matched uniform controls (seed 2026100213, shared prefix, exact actual added
  counts) expose no new retained identity in any case

Every actual new retained identity has zero difference on the original 256
free lanes and an independently replayed appended-lane witness. The search
routine, ordered roots/pools, post-first-refinement seq signatures, masks,
normalization, cost, nonlinear requirement, and top-eight policy are unchanged.
B and C may have different free domains even when their retained identities match.

## Extra-cost mem_ctrl product audit

All 52 union Build identities received 156 fresh proof queries. Whole-original
structural hashing found no output alias for any of the three new identities.
The common bounded Direct scope covers six selected roots, constants, both
phases of saved pools and actually used divisors, and all zero-fresh outputs of
the frozen one/two-AND grammar: 312 Direct candidates including 12 hash extras,
936 queries, 10 positive proved Direct relations.

| Quantity | Initial A | Augmented B/C |
|---|---:|---:|
| Raw Build-only cleanup gain | 22 | 23 |
| Mixed Build/Direct product gain | 27 | 28 |
| Genuine Build same-mixed-set marginal | 2 | 3 |
| New identity same-mixed-set removal marginal | 0 | 3 |

Thus the paired product improvement is **1 AND**. Removing the new selected
recipe from its **same augmented selection** costs **3 AND**. These are distinct
measurements and must not be added or interchanged. Controls reproduce A.
The Direct-only product gains 25 AND. The selected new recipe is root1263,
`[393,2502,-2,2516] -> -4`; its old-arm alternative has gain 2 instead of 3.

Seven distinct input/product/ABC-bound fresh DSEC runs all pass. Exact-graph
DSEC and identical-candidate-set reuse are explicitly recorded. Every emitted
product also passes independent binary-AIGER decoding and 128 arbitrary PI/RO
checks of all PO/RI against the exact selected substitutions. This is a
combinational replay check, not an assertion that original and replacement
products agree on arbitrary states.

The product/Direct/DSEC audit costs an additional 46.61 seconds, of which
12.96 seconds is non-DSEC and 33.66 seconds is DSEC. This is outside the
four diagnostic-case timings and outside any main 120-second transform claim.

## Domain and scope cautions

Predecessor states can be unreachable; that does not invalidate an unrestricted
free witness. Cross-time `(currentPI, previousRO)` recombination is permitted
only in that free domain. Neither predecessor variant enters seq signatures or
a reachable-state teacher. Proof still requires reset0 plus unrestricted
one-step image, with independent current/previous inputs and 1000 conflicts.

All added worlds have zero reset-state and finite known-image-state matches.
The latter only compares against the saved sampled image states; absence is
not proof of being outside the image or being unreachable.

The completed diagnostic uses cooperative Deadline guards and never approaches
its 120-second per-case cap; it does not implement an outer hard-kill supervisor.
No global Boolean Direct exhaustion, native novelty, online integration, or
full55 quality/performance conclusion is established.

## Reproduce

Run from the repository root with the unchanged saved source directories and
ordinary solver available. Use a new output path for every invocation.

```sh
python3 -B -m unittest discover \
  -s research/stran2-guide-20261002/free_domain_diagnostic -p 'test*.py' -v
python3 -B research/stran2-guide-20261002/free_domain_diagnostic/diagnostic.py \
  --ordinary /tmp/nonlinear-anytime-pilot-v1 \
  --source /tmp/image-cegar-diagnostic-v1 \
  --solver /tmp/stran2-query-solver --out /workspace/shared/free-domain-replay
python3 -B research/stran2-guide-20261002/free_domain_diagnostic/audit_products.py \
  --diagnostic /workspace/shared/free-domain-replay \
  --solver /tmp/stran2-query-solver --abc "$PWD/abc" \
  --out /workspace/shared/free-domain-product-replay
```

The product entry is intentionally bounded to the positive mem_ctrl case from
this frozen protocol. It must not silently substitute cases or roots if this
source evidence changes. Raw runs and logs are ignored by Git and remain on
workspace disk; the compact tracked files do not replace those receipts.
