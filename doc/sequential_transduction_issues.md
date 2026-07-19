# Sequential transduction implementation notes

This file records deliberate limitations and unresolved implementation issues.
They are not correctness exceptions: the command rejects a candidate unless the
existing sequential `&scorr` proof engine proves both transaction obligations.

## 2026-07-19: sampled Must1/Must0 search stage

Implemented:

- bit-parallel simulation of random PI traces from all-zero register state;
- RI-to-RO state propagation across simulated frames;
- `M1 = k & other` and `M0 = !k & other` matching for binary AND targets;
- matching of both phases of all topologically earlier CI/AND divisors;
- one-gate `h = d0 & d1` and `h = !(d0 & d1)` candidates, which cover AND,
  OR, and AND-NOT forms when input phases are selected;
- conservative rebuild of signatures after every accepted transaction.

Known limitations and follow-up work:

1. The sampled care is deliberately `C_i=1`.  It does not yet derive the
   sequential observability condition through PO and RI-to-RO paths.  This
   loses optimization opportunities but is safe because formal retention and
   removal proofs remain mandatory.
2. Simulation initializes every RO to zero.  This agrees with the current
   intended reset-based prototype, but GIA register-init metadata and the exact
   initialization semantics used by `&scorr` have not yet been imported.  A
   future implementation must either simulate those semantics exactly or use
   signatures only after a proof-engine-provided reachable-state seed.
3. The target is still a binary AIG AND, not a flattened supergate.  `P` is
   therefore the other immediate fanin, rather than a conjunction of all
   supergate fanins.  Supergate flattening and MFFC victim scoring remain open.
4. Existing-literal matching tests the full topologically earlier CI/AND pool,
   but retains only `-D` nearest matches for formal proof.  Constructed search
   uses a bounded nearest literal base pool of size `-D`; it is not yet an
   exhaustive all-pairs construction over the full network.
5. Duplicate constructed signatures are not canonicalized.  Add a signature
   hash plus an exact structural-cost tie-break before increasing `-D`.
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
