# `&stran2`: CEX teaching signatures (version 1)

## Goal

`&stran2` uses counterexamples to improve the simulation signature that guides
candidate construction.  Counterexamples are not a post-construction filter.
The formal CBS/scorr proof and the non-overlapping commit policy are unchanged.

The main cost target is Build enumeration.  With the default `&stran` settings,
Build consumes `Q * W = 4 * 8 = 32` words per object.  When usable CEX exists,
version 1 gives Build at most eight words while retaining a larger source
simulation for inexpensive ranking and Direct checks.

## Pipeline

1. Run a no-option `&scorr` prepass (`Cec_ManCorSetDefaultParams`, one process).
2. Observe scorr's already packed BMC/resimulation lanes and retain at most
   `min(256, max(64, 64 * Q))` unique reset-reachable traces.
3. Ignore induction traces in version 1 because their initial states are not
   necessarily reset reachable.  Drop reachable traces longer than `W` rather
   than increasing the signature horizon.
4. Project retained register values through the register reduction performed
   by scorr, then freeze the CEX bank.  No CEX learned during transduction is
   fed back into the bank.
5. Once per immutable transduction snapshot, simulate the whole graph over the
   configured random source corpus plus all retained CEX words.
6. For each root, rank the structural divisor reservoir with the full source
   signature and keep the actual Build pool.
7. Select a root-local teaching set from the frozen CEX bank.  A greedy hitting
   set chooses at most 16 traces that refute the most currently uncovered cheap
   wrong hypotheses over the first eight final divisors:
   constants, both literal phases, and two-input AND/OR/XOR functions with both
   output phases.
8. Gather the selected CEX columns plus a deterministic root-local subset of
   reset-reachable random columns into the short Build signature.  This is only
   a column copy; it does not simulate the graph for each root.  Cache the
   packed target/divisor words for later waves.
9. Run existing Build enumeration on the short signature.  Run Constant and
   Existing (Direct) checks on the full source signature because they are cheap.
10. Submit candidates to the existing formal proof and commit flow unchanged.

## Width and fallback

With usable CEX, Build uses `min(8, Q * W)` 64-bit words.  The default therefore
shrinks Build from 32 words (2048 samples) to eight words (512 samples).  The
selected CEX count is root-local and adaptive; unused lanes remain random.

If scorr produces no usable reachable CEX, `&stran2` falls back to ordinary
`&stran` signature construction on the scorr-reduced graph.  It does not force
a short random-only signature.

## Cross-wave behavior

The source simulation is built once for an immutable root pass.  Each root's
sample columns are selected once and their packed target/divisor signature is
cached across all proof waves on that snapshot.  The temporary column-ID list
is then released; later waves only copy the cached words into the shared Build
workspace.  After a committed structural change, the next normal transduction
epoch evaluates the same frozen input/state traces on the new graph; it does
not add or replay newly learned proof CEX.

## Soundness boundary

Simulation only changes discovery and ordering.  Every committed candidate is
still accepted by the pre-existing combinational/sequential proof machinery.
The existing conflict-graph selection and non-overlapping bundle commit are not
changed by `&stran2`.

## Diagnostics

`&stran2` reports the retained/ignored/dropped CEX counts, source and Build
widths, selector calls, roots receiving CEX, selected CEX count, proxy coverage,
and selection/gather time.  In an immutable snapshot, `selector-calls` should
be bounded by the number of live roots even when `root-signatures` grows across
multiple proof waves.
