# Separate mem_ctrl product/attribution audit

Preparation only until independent diagnostic review, exact audit-source/tool
review, and parent GO. This directory does not change the frozen diagnostic,
production or STRAN2.md. The source diagnostic remains the four-case fixed32 run.
The other three cases have no added proved identity and are not audited here.

## Candidate and proof boundary

- Preserve the original 49 qualified identities and form the exact ordered
  cumulative union with 55 additional identities (104 total)
- Authenticate the terminal independent review's pinned file ledger, then the
  unchanged worker completion chain and historical snapshot/source bindings
- Reconstruct the original new-frontier CNF/queries and replay every complete
  SAT model without writing into its source tree
- Recheck every candidate's normalization, reference-count retention cost,
  complete independent free witness and acyclic earlier-original-node inputs
- Freshly query all 104 free/reset/image triples at C1000. Every Build must
  again be SAT/UNSAT/UNSAT. Existing candidate-local models stay candidate-local;
  no fake sample lane or growing free domain is introduced

## Selection, Direct scope and attribution

The frozen selector independently chooses raw products from old49 and union104.
Both arms receive exactly one shared Direct set from the union of those raw
selected roots: constants, both phases of each saved pool and used divisors,
and every zero-fresh literal from the existing full one/two-AND grammar/hash
collector. No free-sample filter excludes a Direct. Fresh reset/image UNSAT and
positive actual retention cost are required; any free UNKNOWN is reported without
claiming combinational or non-combinational classification.

The existing two-stage attribution policy then selects from shared proved
Directs plus each arm's actual raw-selected Builds. This shared scope can change
the old arm's mixed product relative to earlier narrower historical audits;
the new paired comparison uses the same expanded Direct scope for both arms.

Whole-original hashing includes late IDs and complemented aliases. Safe aliases
are classified as existing-logic reuse while preserving the recipe's original
materialization, avoiding unsafe late-ID substitution. Genuine Build also needs
an actually new/live output and at least one live created gate in the current
selection. Every exact product gets independent dependency and 128-world all-CO
substitution replay, plus original-input-to-product DSEC.

Each raw and mixed selection is replayed as full, without newly exposed recipe
identities, without all genuine Build, and without new genuine Build. Removal
arms are subsets of that SAME selection and never invoke reselection. Report
these marginals separately from the old-vs-union product difference and from
candidate gain estimates. An empty-selection baseline isolates unrelated cleanup.

Direct dominance holds all other selected choices fixed and evaluates each
proved same-root Direct. Non-best alternatives are structure-only diagnostics.
The deterministic best cheaper alternative is materialized and DSEC-checked
before calling dominance validated. Costs and changed candidate/selected sets
are reported explicitly.

## Cost, integrity and stopping

One worker; hard 600s total audit deadline includes authentication, preparation,
all proofs/replays/products/DSEC and final checks. Each query batch and DSEC is
given a child-process timeout of at most 120s (or the then-remaining total
time). These are subprocess timeouts, not hard per-operation launch-through-exit
bounds: hashing/replay/cleanup overhead stays inside the hard600s total, and
reported DSEC wall may slightly exceed120s. Entire owned process groups are
terminated on deadline; partial failures are retained, never retried silently.
All costs are additional to the completed discovery experiment. Distinct graph
DSEC calls and exact input/product/ABC/log-bound in-audit reuse are counted
separately. Every emitted product/selection is bound before and after DSEC/reuse,
and final outputs are chained to the externally captured completion digest.

Stop this policy after this single-design audit regardless of mem's result.
No cap changes, new discovery, online/full55 run, global Boolean-Direct
exhaustion or native novelty claim follows.

## Review and execution gate

The external review must contain PASS, the canonical audit source-manifest digest,
protocol SHA256, exact helper dependency map, diagnostic terminal-review SHA256,
solver/build SHA256 and ABC SHA256. The terminal diagnostic review is pinned in
the protocol. No script creates its own review or grants its own GO.

Synthetic tests only (no mem products or actual DSEC):

```sh
UNSAMPLED_SOLVER=/tmp/unsampled-free-model-solver-v2 python3 -B -m unittest discover \
  -s research/stran2-guide-20261002/unsampled_frontier_products -p 'test*.py' -v
```

Only after review and explicit GO, use a NEW top-level scratch output directory:

```sh
python3 -B research/stran2-guide-20261002/unsampled_frontier_products/audit.py \
  --solver /tmp/unsampled-free-model-solver-v2 --abc ./abc \
  --diagnostic-review /workspace/scratch/7e0c7273599c/unsampled-frontier-review/terminal-v1/final_review.json \
  --review AUDIT_REVIEW.json --parent-go RUN_MEM_ATTRIBUTION \
  --out /workspace/scratch/7e0c7273599c/NEW_MEM_ATTRIBUTION_DIRECTORY
```
