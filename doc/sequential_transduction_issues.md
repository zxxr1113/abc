# Sequential transduction implementation notes

This file records deliberate limitations and unresolved implementation issues.
They are not correctness exceptions: the command rejects a candidate unless the
existing sequential `&scorr` proof engine proves both transaction obligations.

## 2026-07-19: sampled Must1/Must0 search stage

Implemented:

- bit-parallel simulation of random PI traces from all-zero register state;
- RI-to-RO state propagation across simulated frames;
- `M1 = k & P` and `M0 = !k & P` matching for positive AND supergate targets;
- matching of both phases of all topologically earlier CI/AND divisors;
- one-gate `h = d0 & d1` and `h = !(d0 & d1)` candidates, which cover AND,
  OR, and AND-NOT forms when input phases are selected;
- one precomputed `Must1/Must0` bitset pair per victim, shared by the full
  existing-divisor scan and the bounded constructed-divisor scan;
- sampled sequential care: flip a target at one trace/frame and resimulate the
  remaining suffix; changed POs or RIs make that target pattern care;
- conservative rebuild of signatures after every accepted transaction.

Known limitations and follow-up work:

1. Sequential care is still sampled rather than formal.  It observes changed
   POs across each recorded trace suffix and conservatively marks an immediate
   RI difference as care.  It therefore improves on `C_i=1`, but it may miss
   reachable traces or care beyond the sampled horizon.  This only affects
   candidate quality because formal retention and removal proofs remain
   mandatory.
2. Simulation initializes every RO to zero.  This agrees with the current
   intended reset-based prototype, but GIA register-init metadata and the exact
   initialization semantics used by `&scorr` have not yet been imported.  A
   future implementation must either simulate those semantics exactly or use
   signatures only after a proof-engine-provided reachable-state seed.
3. Positive-polarity AND supergates are now flattened, so `P` is the
   conjunction of all leaves other than the selected victim.  Complemented
   children correctly remain leaves.  Multi-wire/multi-victim transactions and
   MFFC-based victim scoring remain open.
4. Existing-literal matching tests the full topologically earlier CI/AND pool,
   but retains only `-D` nearest matches for formal proof.  Constructed search
   has an independent base-pool budget `-B` (`0` means all safe literals) and
   a retained-candidate budget `-K`; an all-pairs experiment is therefore
   possible but can cost `O(B^2 W)`.
5. Constructed candidates with identical sampled signatures are now removed
   exactly over the current signature batch.  Different unsampled functions
   can still collide semantically in that batch, so this is a quality-only
   approximation.  Exact structural-cost ordering remains open.
6. The implementation now uses a shared-state local miter: it duplicates the
   target's complete combinational TFO and emits every affected PO and RI as a
   proof boundary, while retaining the original transition relation.  This is
   exact for the current single-target combinational edit.  It does not yet
   construct the explicit union of original/add/final supergate TFOs needed for
   future multi-wire or structural-hash-changing edits.  `&stran -f` runs the
   previous whole-miter proof as a shadow audit.
7. `Cec_ManLSCorrespondence` currently yields a boolean accept/reject to this
   command.  SAT versus UNKNOWN and the resulting CEX are not surfaced, so the
   CEGIS loop cannot yet refine `M1/M0`.

## Invariants to preserve while addressing these issues

- Do not accept a finite BMC-only result as an infinite sequential proof.
- Do not commit on conflict/time/refinement exhaustion.
- Do not assume RO equality is required; the semantic contract is PO traces.
- Any local proof must propagate an affected RI to its corresponding next-frame
  RO and use a sound induction boundary.
- Revalidate candidates after a transaction changes the network snapshot.
