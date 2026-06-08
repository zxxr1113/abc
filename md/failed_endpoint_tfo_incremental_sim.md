# Failed-endpoint TFO incremental simulation for `&scorr -I`

Branch context: `incre_sim_seed`.

This note documents the current `-I` implementation after switching from
CEX-input-delta TFO to SAT failed-endpoint TFO.

## Goal

The implementation is a clean no-skip baseline for incremental simulation.

The key policy is:

- SAT proves one or more SRM outputs are real failed pairs.
- The solver samples the two endpoint values of each failed pair.
- Simulation starts from these endpoint values at the SAT comparison frame.
- Only the frame-aware TFO of these failed endpoints is recomputed.
- Candidate pairs outside this TFO are intentionally left for later SAT rounds.

This is different from full CEX replay.  It does not try to reproduce every
opportunistic split that the same CEX might cause elsewhere in the AIG.

## Data Flow

### 1. SRM construction records endpoint metadata

Files:

- `src/proof/cec/cecCorr.c`
- `src/proof/cec/cecCorrIncr.c`

`Gia_ManCorrSpecReduce()` and `Gia_ManCorrSpecReduce_Active()` still build the
SRM outputs in the usual way.  For each SRM output, they now also optionally
record the raw unrolled endpoint literals in `vOutLits`.

There are two parallel vectors:

- `vOutputs`: original AIG object ids, two entries per SRM output.
- `vOutLits`: raw SRM literals for the same two endpoints, before phase
  adjustment used by the SAT comparison output.

The SAT output may compare phase-adjusted endpoint literals, but `vOutLits`
keeps the raw endpoint values because the persistent simulation table stores
raw object values.

After SRM cleanup, `Gia_ManDupRemapLiterals()` remaps `vOutLits` through the
cleanup result so the solver can sample the correct literals.

### 2. SAT samples failed endpoint values

Files:

- `src/proof/cec/cecSolve.c`
- `src/aig/gia/giaCSat.c`
- `src/aig/gia/giaCTas.c`
- `src/aig/gia/gia.h`

The old solver entry points are preserved.  New wrappers add optional endpoint
sampling:

- `Cec_ManSatSolveMiterOutVals()`
- `Cbs_ManSolveMiterNcOutVals()`
- `Tas_ManSolveMiterNcOutVals()`

When an SRM output is SAT, the solver samples the two raw endpoint literals for
that output and writes them to `vOutVals`.

Layout:

- endpoint 0 of output `Out`: `vOutVals[2*Out]`
- endpoint 1 of output `Out`: `vOutVals[2*Out + 1]`

CBS and TAS sample the values before cancelling assignments, because their
cancel path can clear the data needed to read the model.

### 3. CEX packing records output-to-bit mapping

File:

- `src/proof/cec/cecCorr.c`

`Cec_ManLoadCounterExamplesMapped()` packs CEXes into bit lanes as before, but
also records where each CEX landed:

- `vOutBits = (Out, bit)` pairs

The failed-endpoint simulator needs this because SAT endpoint values are stored
per SRM output, while bit-parallel simulation stores each CEX in a bit lane.

In the local `-I` path, `Gia_ManCorrPerformRemapping()` is now delayed until
fallback.  A successful local endpoint-TFO batch only needs the bit mapping,
not the remapped full `vSimInfo`.

### 4. Persistent simulation table

Files:

- `src/proof/cec/cecInt.h`
- `src/proof/cec/cecCorrIncrSim.c`

`Cec_SeedSim_t` owns a dense persistent value table:

```text
pVal[(frame * nObjs + objId) * nWords + word]
```

It also keeps version-stamped marks:

- `pMark`: dirty keys in the current local batch.
- `pSeedMark`: authoritative SAT endpoint roots in the current local batch.
- `pRootMark`: class roots already scheduled for local refinement.

`iSeedFrame` is set to `pPars->nFrames`.  This is the frame where SRM failed
endpoint pairs are compared.  The resident table is sized for
`pPars->nFrames + 1 + nAddFrames`, matching the main resim depth.

The table is initialized and refreshed only by full sweep:

- first `-I` batch falls back because `pVal` is not initialized yet.
- wide local cones fall back.
- fallback calls `Cec_ManSeqResimulate()` and then
  `Cec_SeedSimUpdateFull()`.

### 5. Local seed collection

File:

- `src/proof/cec/cecCorrIncrSim.c`

For each `(Out, bit)` in `vOutBits`, `Cec_SeedSimCollectEndpointSources()`
reads:

- endpoint object ids from `vOutputs`
- endpoint SAT values from `vOutVals`
- bit lane from `vOutBits`

Then `Cec_SeedSimAddSourceBit()` writes that SAT value into:

```text
pVal[frame = iSeedFrame, objId = endpoint]
```

If the bit differs from the previous persistent value, the endpoint becomes a
dirty seed and is pushed into the TFO queue.  If the value is unchanged, no
downstream recomputation is needed for that endpoint lane.

The seed itself is marked in `pSeedMark`, so evaluation will not overwrite this
authoritative SAT-provided value.

### 6. Frame-aware TFO

File:

- `src/proof/cec/cecCorrIncrSim.c`

`Cec_SeedSimComputeTfo()` walks static fanout from each failed endpoint seed.

Rules:

- AND fanout stays in the same frame.
- RI fanout crosses to the corresponding RO in the next frame.
- The walk stops at the configured resim depth.

The resulting `vDirtyKeys` is the only region recomputed locally.

If the dirty region is larger than `CEC_SEEDSIM_FRAC_NUM /
CEC_SEEDSIM_FRAC_DEN` of the unrolled AIG, the batch falls back to full
sequential resimulation.  The current threshold is 1/5.

### 7. Local evaluation and refinement

File:

- `src/proof/cec/cecCorrIncrSim.c`

Dirty keys are sorted by `(frame, objId)`, which gives frame-major/topological
order for the unrolled AIG.

Evaluation uses persistent side inputs:

- dirty AND nodes recompute from `pVal` fanins in the same frame.
- dirty RO nodes at frame `f > 0` copy from the previous-frame RI driver.
- SAT endpoint roots are skipped because their values were supplied directly
  by the solver.

After evaluation, only dirty frames/classes are considered for refinement:

- dirty class roots are collected once per frame.
- each dirty class is split by comparing `pVal` vectors with
  `Cec_ManSimCompareEqual()`.
- recursive splitting follows the existing class-refinement style.

This is the important narrowing: the implementation refines only classes that
intersect the failed-endpoint TFO.

## Difference from CEX-input TFO

The previous `-I` implementation treated changed CEX input slots as sources.
That can still produce very large cones because a CEX is a broad input
assignment.

The current implementation treats SAT failed endpoints as sources.  It ignores
CEX input deltas for local scheduling.  The CEX is still parsed to know which
bit lane carries each failed output, but it is not used to seed a PI/RO TFO.

This matches the intended experiment:

- split what is in the failed pair's downstream region;
- do not pay for unrelated regions;
- let later SAT rounds handle remaining candidates.

## Skip isolation

`skip` is not part of this baseline.

The incremental simulation path is under `pPars->fIncrSim` / command `-I`.
The skip-failed-resim behavior remains controlled separately by
`pPars->fSkipFailResim` / command `-s`.

For the no-skip baseline, keep `-s` off.

## Profiling Extension Point

The core path does not run a shadow full sweep because that would contaminate
the timing of the local simulation experiment.

To test whether a CEX would also split pairs outside the failed-endpoint TFO,
add a test-only profiling mode around `Cec_ManResimulateCounterExamples()`:

1. run the current local endpoint-TFO path and record the class changes;
2. clone or snapshot the class state;
3. run the standard full sweep on the same packed `vSimInfo`;
4. compare splits whose roots are not in the endpoint TFO;
5. keep this behind a profiling flag and exclude it from timing comparisons.

This is intentionally not in the normal `-I` path.

## Modified Files

- `src/proof/cec/cecInt.h`: `Cec_SeedSim_t` state and new prototypes.
- `src/proof/cec/cecCorrIncrSim.c`: failed-endpoint TFO local simulator.
- `src/proof/cec/cecCorr.c`: main-loop metadata flow and resim integration.
- `src/proof/cec/cecCorrIncr.c`: active SRM endpoint-literal capture.
- `src/proof/cec/cecSolve.c`: standard SAT endpoint-value sampling.
- `src/aig/gia/giaCSat.c`: CBS endpoint-value sampling.
- `src/aig/gia/giaCTas.c`: TAS endpoint-value sampling.
- `src/aig/gia/gia.h`: CBS/TAS wrapper declarations.

