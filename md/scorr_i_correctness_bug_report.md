# `&scorr -i` Correctness Bug Report

## Background

`-i` reuses previous UNSAT results and solves only pairs affected by the
latest class refinement. Its correctness condition is:

```text
Every skipped current SRM pair must still be UNSAT.
```

The debug `-d` mode checks this condition with a separate unlimited-conflict
SAT solver on the skipped-only SRM.

## Bug 1: Unresolved SAT pairs were skipped

Some pairs returned SAT but remained in the same class after packed CEX
resimulation. The old incremental logic only examined `pReprs/pNexts`
changes, so such a pair could have no seed in the next round and be skipped.

The 400k log exposed this at round 11:

```text
INCR-ORACLE BUG: pair=(0,287560), SAT=1
```

Fix:

- Record every SAT/UNKNOWN pair that is still merged after refinement.
- Add both endpoints to the next round's TFO seeds.
- Do not declare convergence while retry pairs remain.
- Log the original `vStatus` for each retained retry pair.

## Bug 2: TFO missed speculative alias dependencies

The original TFO followed only physical AIG fanout edges. However,
`Gia_ManCorrSpecReduce_rec(member)` replaces a class member with its
representative. This creates an additional SRM dependency:

```text
representative -> class member -> physical fanouts of the member
```

If a representative's reduced value changed through another cone, the
physical AIG contained no edge from the representative to its members.
Pairs depending on those members could therefore reuse obsolete UNSAT
results.

The 500k log exposed this at round 15:

```text
INCR-ORACLE BUG: pair=(65186,82228), SAT=1
```

Fix:

- Rebuild the current `representative -> members` adjacency each round.
- Extend TFO traversal through these zero-frame speculative alias edges.
- Continue physical fanout traversal from the reached members.

## TFO Completeness Audit

The current implementation covers every known way the current SRM can differ
from the previously solved SRM:

- `pReprs` change: the affected object is a TFO seed.
- SAT/UNKNOWN still merged: both unresolved endpoints are retry seeds.
- Combinational dependency: static AIG fanout traversal.
- Sequential dependency: RI fanout crosses to the corresponding RO, bounded
  by the SRM unrolling depth.
- Speculative substitution: representative-to-member alias traversal.
- New or rewritten ring edge: forced active by comparing the current edge
  with the saved `pNexts/pReprs` snapshot.
- Removed old alias: the member's changed `pRepr` makes it a seed.
- Constant-class entry or exit: the object's `pRepr` change makes it a seed.

The frame-independent visited mark does not omit a later dependency. Frames
are processed in increasing sequential distance, so an object's first visit
has at least as much remaining unrolling depth as every later revisit.

The traversal remains conservative. It can mark pairs that are not truly
affected, but no remaining missing dependency was found in the code audit.
The user's performance tests also show almost no regression from the alias
fix.

## Validation Status

Code inspection supports the current TFO as a safe over-approximation.
For a concrete benchmark run, correctness is certified only when `-d`
finishes with every skipped pair UNSAT and no `INCR-ORACLE BUG` or UNKNOWN.

The normal limited-conflict solver cannot provide this certificate because a
timeout is UNKNOWN, not UNSAT.
