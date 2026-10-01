# Image-valid equality missed by ordinary scorr: three-flop regression

This bounded standalone experiment changes no production sources or ABC binary.
The project-level interpretation belongs in `STRAN2.md`.

## Circuit and exhaustive proof

All three flops reset to zero. PIs are independent `e,u,v`:

```
q' = e ? u : q
r' = e ? v : r
c' = e ? (u & v) : (q & r)
g  = q & r
PO[0] = c
PO[1] = g
```

The circuit has 3 PIs, 3 flops, 11 ANDs and 2 paired POs. The runner emits a
dense binary AIG, decodes it independently, and checks all 64 state/input rows
against the direct equations. It checks all 8 reset/input rows and all 512
predecessor-state/predecessor-PI/independent-current-PI image rows. Every reset
and image row has `c=g`. There are 32 free-state/input rows with `c!=g`.

An explicit free-state witness is `q=r=1,c=0,e=u=v=0`: current outputs are
`[c,g]=[0,1]`, but the original transition produces `[q',r',c']=[1,1,1]`.
The image property also follows immediately by considering `e=0` and `e=1`.

## Executed result

Saved run: `evidence/run001/result.json`

- Exact command: `&scorr -F 1 -C 1000 -v`, with loaded and resulting AIGs saved
- Both loaded and final paired output literals are `[12,14]`: **NOT_MERGED**
- ABC reports 11 -> 11 ANDs and 3 -> 3 flops
- Initial induction statistics show 1 nonconstant class with 1 equivalence
- First induction round reports `p=0,d=2,f=0`, followed by empty classes
- Independent original-to-after DSEC: **PASS**
- Seven focused unit tests: **PASS**, saved in `evidence/unit_tests.log`
- Total runner wall time: 0.586450281 seconds, including identity hashes and DSEC
- ABC SHA256: `354909c529a36dc7af07f05d07cb09c600a2e1e1c2e4a3a63263c2e1af795342`
- Runner, tests and relevant production-source identities are stored in the
  result, checked again after the run; all unchanged

Pair comparison uses complete literals, including polarity, resolved through
PO indices rather than assumptions about object IDs surviving load/cleanup.
Exit status alone never counts as DSEC PASS.

## What is established, and what remains conditional

This is an executed miss of a reset/image-valid, mathematically 1-inductive
equality. It is not merely a proposed example. It does not by itself capture
the first class-splitting model or frame, and does not establish wb_dma's cause.

The source-consistent explanation is as follows. If the candidate class is
`{c,g}` with earlier RO `c` as representative, speculative substitution changes
the predecessor occurrence of `g` in `c'` into `c`. The speculative update is
therefore `c~'=e?uv:c`. At the witness above it returns 0, whereas the raw
successor `g` is 1. Original-graph CEX replay disagrees at predecessor frame 0
but agrees at frame 1. Ordinary refinement examines frame 0 too.

Source references:

- Candidate ANDs and referenced ROs: `src/proof/cec/cecClass.c:1003-1017`
- Class representative ordering: `src/proof/cec/cecClass.c:239-259`
- Raw-root evaluation still substitutes fanins: `src/proof/cec/cecCorr.c:407-452`
- Free predecessor ROs and two PI frames: `src/proof/cec/cecCorr.c:481-491`
- Induction implication-ring obligations: `src/proof/cec/cecCorr.c:522-553`
- Original-graph replay begins at frame 0: `src/proof/cec/cecSeq.c:143-167`
- Per-frame class refinement: `src/proof/cec/cecClass.c:868-901`

A future diagnostic can snapshot the watched class, output-index/ring-edge
mapping and exact packed CEX lane at the first split, then independently replay
that lane through the original graph. No such hook was added here. Do not
present the algebraic witness in `exhaustive.json` as a solver-returned model.
This experiment makes no novelty claim for reset/image reasoning.

## Reproduce

From the repository root, using the existing ABC binary:

```
python3 -B -m unittest discover \
  -s research/stran2-guide-20261002/speculative_image_toy -p 'test_toy.py' -v
python3 -B research/stran2-guide-20261002/speculative_image_toy/run_toy.py \
  --abc ./abc \
  --out research/stran2-guide-20261002/speculative_image_toy/evidence/my_run \
  --seconds 30
```

The output directory must not exist. The scorr and DSEC child processes share
one deadline of at most 30 seconds. No SAT solver helper or compilation is
needed because the complete truth-table proof is tiny.
