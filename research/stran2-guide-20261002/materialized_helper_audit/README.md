# Materialized-helper ordinary-scorr audit

This bounded comparator uses only the selected anytime-v2 recipes for the
predeclared b03, b20_opt and wb_dma cases. It asks whether ordinary signal
correspondence obtains a relation when its expression is already present. It
makes no new area, native QoR, general solver-completeness, or publication claim.
The project-level report remains `STRAN2.md`; this is the local experiment's
reproduction/evidence description.

## Frozen result

| Case | Selected pairs | Paired COs merged | NOT_MERGED | Rounds | Sweep wall (s) | Augmented DSEC |
|---|---:|---:|---:|---:|---:|---|
| b03 | 5 | 3 | 2 | 2 | 0.0643 | PASS |
| b20_opt | 57 | 13 | 44 | 2 | 0.7187 | PASS |
| wb_dma | 1 | 0 | 1 | 2 | 0.2410 | PASS |

All three reached exact loaded-AIG structure fixed point in the second round.
There were no sweep/checker timeouts or errors. Six materializer tests pass.
The 47 non-merges remain inconclusive. No new candidate discovery was performed.

`evidence/results.json` and per-case `result.json` retain exact candidate and
free-witness identities, source checkpoint and input hashes, original and
augmented graph hashes, each command, output, log, paired literal values and
independent DSEC results. All 63 saved free witnesses were replayed. A further
128 arbitrary PI/RO assignments per case checked every original PO/RI and every
root/helper pair. These simulations supplement the exact construction and
DSEC; they do not replace formal proof.

## Construction and proof boundary

The original AND list, original output prefix, latch-input literals, input order,
and zero reset are copied exactly. Each selected h uses the original source IDs;
no original root is replaced. Original gates are seeded into the structural hash,
then h is appended/reused and paired POs `(root,h)` are added after all original
POs. Latch inputs remain in their original separate AIGER latch section. Added
POs make every helper observable and live.

The paired-CO comparison uses the complete AIGER literal, including its phase
bit. The helper's recipe output inversion is already applied, so `root=~h_raw`
correctly merges when their normalized output literals agree; same node with
opposite phase does not count. Tests include both outcomes. Before scorr all 63
pairs have distinct output literals and independently replayed free-state
counterexamples. DSEC compares the entire augmented-before graph against the
final augmented-after graph, including every added output, before a merge is
counted as ordinary-scorr proof evidence.

Let `D(s,x)=root(s,x) XOR h(s,x)` and `P(s)=forall x. D(s,x)=0`.
The saved certificates prove `P(reset)` and
`forall s,u. P(T(s,u))`, with current `x` independent of predecessor input `u`.
The latter implies `P(s) => P(T(s,u))` without even needing the antecedent.
Every accepted relation is therefore 1-inductive. Failing to obtain its merge in
one heuristic, finite-resource scorr run does not establish stronger logical
proof power for the image checker. It does expose a distinction between the
mathematical proof class and practical correspondence-class/refinement behavior.

This implication is consistent with the initialized-base/uninitialized-last-frame
criterion in [DATE 2024, Section III.E, Theorem 1](https://people.eecs.berkeley.edu/~alanmi/publications/2024/date24_seq.pdf).
The [journal extension](https://people.eecs.berkeley.edu/~alanmi/publications/2025/tcad25_seq.pdf)
provides wider SODC, assumption and resubstitution context. This audit is not a
novelty claim about either principle.

## Important wb_dma structural-alias qualification

The selected wb recipe is root759, recipe `[1144,1508]`, out `-2`.
On the full original graph it hashes to existing node3895 (literal7790), whose
fanins are literals1508 and1144, nodes754 and572. Both fanin nodes precede759;
node3895's transitive fanin does not contain root759. Thus the auxiliary graph
needs zero fresh ANDs for this h. A later original ID alone does not imply a
cyclic or unusable replacement.

This is an exact whole-graph structural alias, not a claim that scorr proved the
root relation. The earlier product's fresh-gate/Direct interpretation was under
an earlier-ID reconstruction/search boundary and is pending a separate global
structural-alias/positive-cost audit. Do not use this comparator to claim the
previous wb benefit inherently requires inventing a new expression.

## wb_dma miss diagnosis, with uncertainty retained

One additional, separately costed `&scorr -F 1 -C 1000 -v -w` replay took
0.0640s and produced exactly the primary first-round graph structure. Its
induction statistics contain zero `f` (UNKNOWN/failure) entries in every round.
The candidate classes eventually become empty. There is no observed
conflict-limit failure explaining this particular run.

Source inspection establishes that the default ordinary entry places every AND
into the candidate-constant class, refines using zero-reset sequential simulation,
uses ring obligations, calls CBS for induction and TAS for a nonempty base check.
`-w` prints flop equivalences only; it does not supply a per-node/per-obligation
trace. The exact later class membership of nodes759/3895, whether their direct
pair was ever attempted, and the individual obligation/model that removed the
relation are **UNKNOWN** from these logs. The reset/image proof plus initialized
simulation source suggests they should initially survive in the same class,
but that is a source/mathematical inference rather than captured membership.

A plausible source-level loss mechanism is that ordinary induction-CEX full
resimulation refines classes starting at predecessor frame0. That state is not
necessarily reachable or in the transition image. An image-valid but free-state
inequivalent relation can therefore split during such resimulation. The exact
causal CEX/ring edge in this run was not observed, so this remains a hypothesis.
The final helper literal3058 is a renumbered signal, not evidence of root/helper
merging. No production hooks, solver changes, case tuning, or extra case runs
were introduced. See `evidence/wb_diagnostic.json` and
`evidence/parameter_evidence.json` for source lines, hashes and the saved replay.

## Parameters and reproduction

The exact repo HEAD was `67f9432` and ABC SHA256 was
`354909c529a36dc7af07f05d07cb09c600a2e1e1c2e4a3a63263c2e1af795342`.
No production source changed for this comparator. Ordinary `&scorr`, rather than
`&scorr2`, ran with explicit `-F 1 -C 1000 -v`. Source and all six runtime headers
confirm Fr1, Conf1000, Lcorr0, Ring1, CSat1, Oracle0, Dyn0; prefix defaults to0.
The shared sweep budget is at most120s per case, including command I/O/reloads.
If all pairs merge the experiment stops; otherwise the identical command repeats
on its output until exact loaded graph equality or that total budget. Each final
augmented DSEC has its own separately reported120s maximum. Sweep wall above
includes load/write, not isolated engine CPU time; it is not a speed benchmark.

```sh
STRAN2_FROZEN_PACKAGE=/tmp/nonlinear-anytime-pilot-v2/source \
  python3 -B -m unittest discover \
  -s research/stran2-guide-20261002/materialized_helper_audit -p 'test*.py' -v
python3 -B research/stran2-guide-20261002/materialized_helper_audit/audit.py \
  --run /tmp/nonlinear-anytime-pilot-v2 \
  --inputs research/stran2-guide-20261002/inputs/first_seq \
  --abc ./abc --out /tmp/materialized-helper-audit-user
```

The output directory must not exist. The three-case cohort is fixed in code;
there is no per-case tuning option. The source runtime and checkpoint receipts
are hash-checked against the frozen anytime-v2 provenance before use. All new
code and retained evidence live under this directory. Original anytime/CEGAR,
production source and `STRAN2.md` were not edited by this audit.
