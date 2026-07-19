# Alan meeting brief — 2026-07-19

## 1. New project: quality-oriented `&scorr` transduction

**Question.** Can a new divisor/wire be deliberately synthesized so that adding it preserves sequential behavior, but makes a chosen existing fanin redundant and therefore removable?

- References: *Scalable Sequential Optimization Under Observability Don't Cares* (SODC) and *High-Effort Logic Synthesis Using Randomized Transduction*.
- Proposed difference: begin from a victim edge, derive an incomplete specification for the new divisor `h` (`M1 => h=1`, `M0 => h=0`), then use bit-parallel simulation to screen existing/constructed divisors before formal proof.
- Next implementation: constant-redundancy baseline -> persistent pattern/CEX database -> specification-guided candidate construction -> CEGIS -> progressively larger local proofs using `&scorr` base/induction infrastructure.
- Main question: should the first high-quality version prioritize broad simulation-guided divisor construction, or retain a bounded proof/window budget to control runtime?

## 2. `-K`: strict final correctness audit for `&scorr`

`-K` is an untimed, fail-closed final audit, not a replacement for `dsec`.

1. After refinement, rebuild a **complete static SRM** from the final correspondence relation; it does not reuse the dynamic core or incremental active mask.
2. Construct the complete inductive-step mismatch formula and the complete base/init mismatch formula.
3. For each formula, OR all mismatch outputs and run Kissat without the optimization proof budget. Both formulas must be UNSAT.
4. Only then reconstruct the reduced AIG. SAT or UNKNOWN returns the original AIG rather than an uncertified reduction.

Thus it establishes that the final relation holds initially and is transition-closed; together with phase-correct reconstruction, this proves sequential equivalence under the same initialization semantics. Current documented evidence: 324 outputs passed `dsec`; 19 additional outputs passed both `-K` base and step audits (343/343 completed validation paths). Scope: direct, zero-prefix sequential GIA path, `F >= 1`; it is a strict SAT-based audit, not an independently replayable DRAT/LRAT certificate.

## 3. `-Y`: CBS-first, TAS-rescue heuristic for the `-D` regression

**Root cause.** Dynamic `-D` moves proofs to a large resident core. CBS can hit its fixed justification limit, return `UNKNOWN`, and conservatively discard true candidate correspondences; QoR then regresses.

**Mechanism.** Run CBS first. Only when it returns `UNKNOWN`: reject TAS on oversized cores; otherwise probe at most eight roots with TAS. Retry only when the probe resolves at least 75%, under deterministic structural and retry budgets. CBS SAT/UNSAT results are never changed; TAS can only replace CBS `UNKNOWN`.

**Recorded targeted results.**

| Case | CBS-only (ff/AND) | `-Y` (ff/AND) | Interpretation |
|---|---:|---:|---|
| `pals`, F=1 | 473 / 8974 | 315 / 7311 | 186/186 CBS UNKNOWN roots rescued; matches TAS-only QoR |
| `pals`, F=2 | 482 / 9090 | 279 / 6800 | matches TAS-only QoR |
| `pals`, F=4 | 482 / 9107 | 291 / 6985 | 5616/5630 UNKNOWN roots rescued |
| `transmitter`, F=1 | 3469 / 112601, 5.90s | same, 5.94s | TAS correctly suppressed; TAS-only did not finish in 144s |

The saved experiment set demonstrates recovery of the three documented `pals` QoR regressions without sacrificing the fast CBS path on large/non-beneficial cases. It is not yet a full-suite count of “all regressions”; that needs the final benchmark CSV. `pals` and `transmitter` both passed `-Y -K` base/step audit.

## 4. Paper discussion
