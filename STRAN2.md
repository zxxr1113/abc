# `&stran2` development guide

This file is the single source of truth for the current implementation and
latest measurements. Historical exploration notes are intentionally omitted.

## Current state

- Production tree: `/mnt/home/zhaoxiran/abc`
- Branch: `codex/stran2`
- Production output/multi-cut integration commit:
  `b9a3ee615fe1283f7a3a8c6c9f2c440755c5bbd3`
- That commit's measured binary SHA256:
  `414e6b790a768dbb1ab0707735cac5286fbba9f7bab236cd2b31c11dcbf09ca1`
- Earlier integrated F/C commit: `55e476c65c6c29a26399e8e8c63566f972867de6`
- Earlier module-refactor validation binary SHA256:
  `a19f03ddc156795692ff41e9a3bd5548979a2d6fff349164774e17e8fc93ceab`
- Build: `make ABC_USE_NO_READLINE=1 -j8`

`&stran2` now applies `-F/-C` uniformly to its initial integrated `scorr` and
to every later transaction proof. The no-option `&stran2` default remains
F1/C1000. `&stran` keeps its F1/C100 default. The permanent-output tail is
also off by default (`-R 0`, `-Y 0`). `-Y 1 -R 6` explicitly enables the
Direct output tail; `-Y 1 -R 27` runs that same Direct prefix followed by the
graph-costed multi-structural-cut Kit/BDC tail.

The production path contains the validated strict prefix, reachable-CEX
teaching, TFO divisors, immutable-page reuse, Kit/BDC construction, optional
ODC, optional signature guidance, strict-CEX feedback, and schema 9/10
profiling. Archived prototype hooks are not part of this tree.

## Algorithm and proof boundary

The pipeline is:

1. `&stran2` runs reset-aware signal correspondence and freezes retained CEX
   traces after register remapping.
2. One arbitrary-state combinational root pass discovers and proves candidates.
3. Sequential epochs use immutable snapshots. Direct, Existing and Build
   candidates are proved in shared batches, then profitable non-conflicting
   edits are committed to a fixed point.
4. Optional ODC processing substitutes a candidate through a spatial fanout
   window and proves every exit obligation before commit.

CEX and auxiliary signatures are construction/filtering evidence only. They
never certify an edit. Strict candidates must prove root equality. ODC changes
the obligation to preservation at all affected window exits, so it can admit
reachability- and observability-dependent replacements that strict root
equality cannot.

Every commit is checked against the current graph and must have positive exact
cleanup gain. Assertions encode proof and ownership invariants; do not replace
them with silent fallbacks.

Main implementation files:

- `src/proof/cec/cecTrans.c`: public entry points and root/epoch orchestration
- `src/proof/cec/cecTranInt.h`: private types, counters and shared declarations
- `src/proof/cec/cecTranCex.h`: retained CEX and trace simulation/selection
- `src/proof/cec/cecTranTfo.h`: TFI/TFO divisor collection and ranking
- `src/proof/cec/cecTranBuild.h`: construction and root discovery
- `src/proof/cec/cecTranCandidate.h`: candidate recipes and canonicalization
- `src/proof/cec/cecTranProof.h`: shared CBS/scorr proof
- `src/proof/cec/cecTranGain.h`: exact MFFC/gain and support accounting
- `src/proof/cec/cecTranCommit.h`: conflict selection and bundle commit
- `src/proof/cec/cecTranOdc*.h`: ODC care, window proof and composition
- `src/proof/cec/cecTranProfile.h`: profile emission
- `src/proof/cec/cec.h`: public parameters
- `src/aig/gia/giaResub.c`: native recipe iterator and polarity behavior
- `src/proof/cec/cecTranCexCompress.h`: CEX corpus handling
- `src/proof/cec/cecTranStrictCex*.h`: strict CEX feedback and active queries
- `src/proof/cec/cecTranStrictGuide.h`: strict auxiliary signatures
- `src/proof/cec/cecTranSigGuide.h`: optional ODC signature guide
- `scripts/stran_profile.py`: stable profile parser
- `scripts/bench_scorr_then_stran.py`: benchmark driver

The `cecTran*.h` files above are private implementation fragments included by
`cecTrans.c`; they deliberately remain one translation unit so the refactor
does not widen the C API or change link-time behavior.

## Supported parameters

The common measured configuration is:

```text
-F 1 -C 1000 -b 100 -S -1 -N 20 -B 16 -T 8 -D 1 -K 8
-Q 4 -W 8 -q 20 -j 5 -w 8 -V 0 -E 747118613 -d -p
```

Add `-k -J -O 0 -L 16` for the measured ODC phase. The corresponding launch
wrappers are `scripts/run_stran2_quality.sh`,
`scripts/run_stran2_strict_cex.sh`, and `scripts/run_stran2_signature.sh`.

Important controls:

- `-F`: BMC/induction depth for integrated scorr and transaction proofs.
- `-C`: per-obligation correspondence conflict limit for both locations.
- `-Q/-W`: trace words and reset-reachable trace horizon.
- `-B/-K/-N`: ranked material, TFI depth and recipe-size limits.
- `-q/-j/-w`: Build horizon, proof micro-batch size and sequential epochs.
- `-d`: complete-fanin TFO divisors in sequential discovery.
- `-k -J`: ODC phase with frozen fanout-boundary proof/commit.
- `-p`: schema-stable profiling, including `stran2_initial_scorr_*`.

The large `E747118613` preset is a measured bundle, not a general public API.
Its active bits are 1, 4, 16, 8192, 524288, 8388608, 67108864, 134217728 and
536870912. Preserve it when reproducing the latest data; new work should prefer
named command options over adding another exploration bit.

Recommended policy from current evidence:

- Keep F1/C1000 as the compatibility/default setting.
- Use F2/C1000 as the optional balanced deeper-proof setting.
- Do not use F4 globally by default: it loses coverage, costs substantially
  more and does not dominate F2.
- Raising C globally is not the main quality lever. If revisited, escalate only
  selected hard obligations and report UNKNOWN counts and runtime.

## Latest measured results

### Fast35 F/C matrix (2026-09-13)

All listed optimization runs passed. All products passed DSEC; the one raw F4
ODC undecided result was discharged independently with `dsec -r -m -T 1800`.

| mode | F/C | final AND sum | Build/source | total SEQ/source |
|---|---:|---:|---:|---:|
| strict | 1/1000 | 18,319 | 7.057889% | 7.696956% |
| strict | **2/1000** | **18,198** | **7.071088%** | **7.713980%** |
| strict | 2/10000 | 18,201 | 7.026736% | 7.571828% |
| strict | 4/1000 | 18,219 | 6.821617% | 7.493539% |
| strict | 4/10000 | 18,199 | 6.794697% | 7.399750% |
| ODC | 1/1000 | 17,507 | 8.958466% | 9.597533% |
| ODC | **2/1000** | 17,393 | **9.599563%** | **10.242455%** |
| ODC | 4/1000 | **17,365** | 9.366312% | 10.038234% |

C10000 reduced UNKNOWNs but did not monotonically improve final QoR. At F4,
initial-scorr time rose from 10.960 s at C1000 to 35.932 s at C10000.

### Quick268 frame attribution (2026-09-14)

The complete matrix has 12 arms, 3,216 integrated invocations and a 60-second
timeout per invocation. Common-PASS difference-in-differences for F4 versus F1:

| added factor | common PASS | final-AND interaction | Build interaction mean |
|---|---:|---:|---:|
| CEX over base | 203 | -1,450 | +0.013285 pp |
| TFO over base | 196 | -420 | +0.008290 pp |
| TFO+CEX over base | 195 | -1,717 | +0.024776 pp |
| ODC over TFO+CEX | 101 | -223 | **+0.153419 pp** |

The ODC-by-frame interaction is real but sparse: median interaction is zero,
and ODC completes only 38--43% of Quick268 within 60 seconds. F2 gives nearly
the F4 ODC Build gain with materially better coverage and runtime.

Initial scorr on the 257 complete cases reinforces the non-monotonic result:

| F/C1000 | result AND / registers | BMC / induction UNKNOWN | time |
|---|---:|---:|---:|
| F1 | 3,927,909 / 351,772 | 2,547 / 32,244 | 327.948 s |
| **F2** | **3,913,809 / 351,694** | 6,076 / 39,651 | 534.322 s |
| F4 | 3,918,085 / 351,703 | 18,126 / 54,648 | 1,059.414 s |

### Interpretation

CEX changes observations and TFO changes spatial material, but both retain the
same strict root-equality proof. Deeper F helps only when a useful equality is
not already one-inductive. ODC admits a broader class of sequentially valid
edits at window exits, so multi-cycle reachability/observability constraints
can make extra frames useful.

Clock-like structure alone is not predictive. AIGER has one transition relation
and usually encodes RTL clocks as enables/self-holds or inputs. `qspiflash`
divider properties benefited from deeper ODC proof, while `dblclockfft` did
not. A future policy needs source-labelled, design-deduplicated families and
should escalate only ODC obligations with a measured multi-cycle signature.

## Evidence review and research proposals (2026-09-14)

This is a read-only algorithm review of production commit
`89858c9e93c1ccde6b06f42b62909fde12c57d09` and completed experimental evidence.
Only this report was edited. No algorithm, build, benchmark, or new task was
started. The proposals below require a separate user decision; they are not
changes to the production proof boundary or default configuration.

The user identified task `01a09e87-3745-7540-aa19-a5a9e29026a6` as the output
proof experiment. Its explicitly authorized prototype tree is
`/mnt/home/zhaoxiran/abc-relobs-20260914`; it is not the production baseline.
At the time of the initial review that task had been stopped by the user. Its then-last tested frozen commit was
`cc295e594801a5144812473b218b1b2751d6b569`. A later SAT-core helper in its
working tree was unbuilt/unvalidated and had no measured quality result then.
The task subsequently resumed; the 2026-09-15 review below supersedes that
status, while preserving the historical comparison populations.

### What the completed comparisons establish

All percentage changes below are equal-case means of gain/source_and, in
percentage points. Final AND delta means candidate minus matched control;
negative is better. Different row populations must not be pooled.

| experiment | matched verified products | final AND delta | Ordered Build mean delta |
|---|---:|---:|---:|
| native ODC polarity completion | 35 | 0 | 0 pp |
| native ODC separate proof views | 35 | -19 | +0.081854 pp |
| spatial reconvergence cut | 35 | -8 | -0.006816 pp |
| spatial exit shrinking | 35 | +10 | -0.013937 pp |
| spatial edge cut | 35 | -3 | +0.010327 pp |
| output guarded Build, versus its rebuilt control | 35 | -63 | +0.578386 pp |
| fixed output-Direct prefix, then output trace Build | 27 | -56 | +0.641175 pp |
| same Direct prefix, output versus window trace Build | 19 | +23 | -0.469635 pp |

Native-care and spatial controls reproduce 17,393 AND / 1,771 latches,
Ordered Build mean 9.599563%. The output task's rebuilt control is 17,392
AND, mean 9.590762%; it reports the small reproduction differences. Do not
silently use 17,393 as its measured paired control. The 27-product row comes
from 35 completed attempts with eight original 1800s timeouts. The 19-product
row is an interim common independently verified subset of an interrupted
boundary comparison, not a full-fast35 dominance result.

Polarity changes ODC generated/proved from 577,800/8,359 to 591,539/8,368,
but selected/gain stay 457/805 and all final circuits are unchanged. Separate
proof views produce 1,999,016 candidates and 8,685 proofs, selecting 474 for
824 gain. Their paired pipeline time ratio is mean 2.508345, median 1.058466,
with pooled time ratio 2.097932. Candidate growth alone is not quality.
The initial care-only comparison has 34 PASS and one timeout: 16,911 ->
16,936 AND on those 34, not evidence that dropping more guidance helps.

The spatial first-snapshot audit covers 8,588 roots. Native MUX/XOR/buffer
barriers are absent in this corpus. Capacity affects 142 distinct roots,
RI boundaries 4,231, and depth boundaries 4,805; causes overlap. Thus a
syntactic gate-support limitation exists in code, but was not an active
quality bottleneck on this corpus. Deeper D8 and capacity variants each have
34 PASS plus one timeout, with respective matched final AND regressions of
5 and 6. These experiments do not establish a broad benefit from expansion.

The output task's initial 30 independently verified mixed-path products save
2,015 AND, of which 1,861 is attributed to Direct and 154 to Build. This
must not be described as 2,015 AND of new Build or state-divergence gain.
After the fixed Direct prefix, the 27-product comparison is 4,135 -> 4,079
AND, 931 unchanged latches, and Ordered Build gain 1,149 -> 1,205. Its 51
Build commits split into root-valid 29/31 (count/gain), window-only-valid
13/14, and genuinely state-divergent 9/11. Summed pipeline times on those
same PASS products are 3,219.673 -> 7,921.738 seconds (2.460417x); this omits
timeout costs and independent final validation, and is not a controlled
throughput measurement.

Evidence authorities:

- `/mnt/home/zhaoxiran/script2/evidence/20260914_odc_native_care/matrix_analysis.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_spatial_odc/20260914/online_analysis.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_spatial_odc/20260914/termination_root_analysis.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_relobs/20260914/metrics.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_relbuild/20260914/metrics.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_relbuild/20260914/after_direct_verified27.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_relbuild/20260914/first_snapshot_boundary_audit.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_relbuild/20260914/cone_opportunity_audit.json`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_relbuild/20260914/user-stop/manifest.json`

### Code findings and falsifiable next questions

1. **Relational feedback is translated into point assignments too early.**
   The prototype's `Cec_TranTbReady` branches a clause system into partial
   on/off assignments; `Cec_TranTbSearch` then calls the native iterator.
   For failed recipe f on a real input trace, the learned necessary condition
   is OR_t[h(x_t^f) != f(x_t^f)], not an independently mandatory value at every
   frame. A care mask cannot generally express that disjunction. On 391
   matched first-snapshot roots with identical material/MFFC and no Direct
   seed, window/output feedback yields 8,207/259 unit clauses and
   29,523/76,517 explored branches. Six proved window recipes (3--7 gates,
   seven AND total first-snapshot gain) satisfy every output clause but are
   never proposed before the 320-branch cap. Causal temporal slicing recovers
   one; five remain absent. This is a demonstrated construction omission.
   A proposed response is a clause-aware native constructor plus a retained
   window-guided construction lane. The window lane may guide generation
   without imposing window equality on the output lane. A retained candidate
   set does not guarantee monotone final QoR after different commits.

2. **Generation cost and commit cost use different notions of area.**
   `Cec_TranDependencyIteratorStart` limits raw recipe size to
   min(N, MFFC-1); discovery also rejects nMffc-nGates <= 0. Later,
   `Cec_TranCandFrozenGainWithRefs` counts physically new hashed nodes and
   recomputes the removable cone with retained dependencies. Thus physically
   profitable shared recipes need not satisfy the earlier raw-size bound.
   The frozen output audit includes a three-gate recipe with one physically
   new gate, showing the two costs differ; it does not prove that a candidate
   excluded by this bound would improve the full batch. First measure such
   excluded positive-exact-gain recipes. A future constructor could price
   existing AIG subgraphs and retained support during search, while retaining
   the final exact audit. This is logic-area optimization, not cache reuse.

3. **ODC composition removes alternatives before gain selection sees them.**
   `Cec_TranOdcFanoutRound` calls `Cec_TranWindowPoolAdd` in frontier order;
   the latter reserves the full window and external reads. Only its SafePool
   reaches `Cec_TranRootConsumeProved`, which already performs exact-cost
   conflict selection. The measured control has 8,359 proved candidates,
   7,868 composition conflicts, 491 SafePool candidates and 457 selections.
   Same-root alternatives are included in conflicts, so 94% conflicts is
   NOT 94% lost independent gain. Diagnose a frozen proved population by
   distinct root, exact gain and cross-root proof dependency. A proposed
   change would combine compatibility and gain selection, or reprove a
   chosen bundle; dropping composition checks is not justified.
   The output prototype has a related, different limitation: serial search
   commits the first proved positive-gain recipe rather than comparing a
   portfolio. Keeping serial proof does not require keeping first-success
   quality selection.

4. **Material selection still optimizes an older proxy objective.**
   `Cec_TranRankDivReservoir` scores each divisor independently by separated
   old-root on/off pairs. Production has a TFO core rescue and limited
   construction-aware alternatives, so it is not simply a naive top-B pool.
   Nevertheless its default TFO rescue uses strict observed equality, and
   complete long-trace guidance is applied after binding the pool. The output
   trace prototype also ranks/truncates its pool before learning its clause
   system. A small separating support need not be the cheapest realizable
   AND DAG; the best support under root equality need not serve a temporal
   output relation. Proposed diagnosis: establish a useful recipe requiring
   rejected material on a frozen snapshot, then study relation-aware,
   implementation-cost-aware support selection. Merely increasing B is not
   evidence for the mechanism. The six current construction omissions have
   identical pools, so material selection cannot explain those six.

5. **Single-root positive-gain construction cannot exploit all joint sharing.**
   A longer-term proposal is small multi-output heuristic resynthesis with
   shared intermediate nodes, not mandatory SAT exact synthesis. Start by
   measuring joint removable cones and sharing opportunities. Preserve the
   output relation of the complete selected transformation and account for
   proof composition. No result in the current review quantifies this route's
   additional gain. Zero-cost structural moves are another literature-backed
   possibility, but likewise lack project-specific opportunity evidence.

The first recommendation has actual missed-candidate witnesses. Cost and
selection mismatches have direct code evidence, but their additional final QoR
on the current baseline has not been measured. Earlier selection experiments
did measure local losses and small online changes on an older baseline; see
the historical qualification below. Support selection and joint reconstruction
remain research hypotheses for additional gain on the current baseline.
Before further full batches, require a general mechanism and a frozen witness
that isolates it; then use matched fast35 products, explicit timeout coverage,
Direct/Build attribution and independent whole-product proof. Treat related
original/optimized circuits as families when assessing generalization.

### Literature used in this review

- [Mishchenko and Brayton, SAT-Based Complete Don't-Care Computation for Network Optimization, DATE 2005](https://arxiv.org/pdf/0710.4695): complete node flexibility versus optional reconvergence-aware windows; it does not establish our temporal state-divergent transformation.
- [Mishchenko et al., Using Simulation and Satisfiability to Compute Flexibilities in Boolean Networks, TCAD 2006](https://people.eecs.berkeley.edu/~alanmi/publications/2005/tcad05_s%26s.pdf): CDCs, SPFDs and distinguishing-power conditions for support selection.
- [Testa et al., Extending Boolean Methods for Scalable Logic Synthesis, IEEE Access 2020](https://si2.epfl.ch/demichel/publications/archive/2020/access.pdf): Boolean filtering, forward functional flexibility and representation-dependent resubstitution methods.
- [Simulation-Guided Boolean Resubstitution, 2020](https://arxiv.org/pdf/2007.02579): simulation-driven proposal and SAT validation.
- [A Simulation-Guided Paradigm for Logic Synthesis and Verification, TCAD 2021](https://people.eecs.berkeley.edu/~alanmi/publications/2021/tcad21_sim.pdf): expressive observations guide construction; observations and validation remain distinct.
- [Solar-Lezama et al., Combinatorial Sketching for Finite Programs, ASPLOS 2006](https://people.csail.mit.edu/asolar/papers/asplos06-final.pdf): general CEGIS architecture. The first-difference temporal clause is the prototype's own derivation, not a result attributed to this paper.
- [DAG-Aware AIG Rewriting, DAC 2006](https://people.eecs.berkeley.edu/~alanmi/publications/2006/dac06_rwr.pdf): actual DAG sharing, dereference/reference gain and optional zero-cost moves.
- [Costamagna et al., Post-Mapping Resubstitution, 2024 manuscript](https://people.eecs.berkeley.edu/~alanmi/publications/2024/iwls24_resyn_sc.pdf): dependency cuts, support/resynthesis separation and complementary structural/local/global searches. Mapped-area results are not an estimate of our AIG gain.
- [Riener et al., Boolean Rewriting Strikes Back, ASP-DAC 2022](https://people.eecs.berkeley.edu/~alanmi/publications/2022/aspdac22_rwr.pdf): multi-output heuristic Boolean resynthesis without requiring exact synthesis. Its combinational results do not predict our sequential gain.

### Historical small-cut evidence and bounded exact construction

This follow-up review inspected completed task summaries, current source and
primary literature. Historical numbers below were recovered from task records;
the old raw evidence directories are no longer present in the active evidence
tree and were not independently revalidated in this review. No new experiment,
algorithm implementation or task was started.

Task `01a08ff5-180b-7ca3-8463-8aa2e48cb009` reported the following fast35 tail
experiment on identical already-optimized snapshots totaling 18,697 AND:

| subsequent optimization | final AND | extra reduction versus continued native |
|---|---:|---:|
| continued native | 18,629 | 0 |
| same added small cuts, old observations | 18,579 | 50 |
| full small-cut information mixed into native search | 17,480 | 1,149 |
| separate full-small-cut construction tail | 17,509 | 1,120 |
| independent ABC rewrite -l to positive-gain fixpoint | 17,254 | 1,375 |

The prototype selected at most four cut inputs from legal divisors and used
native/Kit/BDC construction, followed by existing proof and gain checks. It did
not use SAT synthesis or the rewrite library. The four prototype/control arms
and two flows reportedly passed all 280 DSEC checks; rewrite products also
passed CEC/DSEC. These are tail results after old stran2, not standalone rewrite
versus stran2 results. The full-information versus old-observation comparison
supports a construction-guidance gap. Later strict CEX feedback addressed this
mechanism, so the historical 1,149 AND is not an estimate of remaining gain on
the current 17,393-AND baseline or the separate output-proof prototype.

Task `01a08ff4-804b-7122-8d54-53e6eff17f29` reported a stronger single-root
recipe experiment saving 23 final AND on an old fast35 baseline; an additional
candidate-slot control already saved 19. It also found a proved four-gate
shared-internal-DAG witness on the same pool/core, improving exact root gain
from one to two. This establishes a bounded construction omission, but does
not attribute all online improvement to the new constructor.

Task `01a08ff4-38e0-76c1-a782-34e81abe08c8` had already studied ODC selection:
on a frozen b04 case, the existing SafePool optimum was 17 versus 23 when
selecting before that restriction, and joint proof found a feasible 26.
However, online fast35 final AND changed only 18,697 -> 18,686 / 18,692 for
the two variants, while their reported mean Ordered Build metrics regressed.
This is measured historical local opportunity with weak online transfer, not
an untested selection idea or a demonstrated large current-baseline gain.

Current `Cec_TranCollectRootIsfCandidate` constructs a small observed core via
Kit/BDC; the native iterator separately searches the broader material pool.
Neither constitutes a complete bounded DAG search. Classic ABC rewrite uses
cut truth tables, library realizations and graph-aware cost evaluation;
online SAT synthesis is a distinct optional candidate generator. The repository
also contains `twoexact`, but adapting an exact engine to stran2 care, legal
divisors and temporal relational clauses is not a demonstrated drop-in change.

A proposed quality study would pair native and bounded exact construction on
identical frozen supports/specifications, separately varying additional cut
views. It should preserve formal validation, distinguish strict truth from
observed care and temporal relations, and measure actual new-node/deletion
gain rather than only isolated recipe size. Include an extra-slot control and
an independent rewrite tail on the current baseline. SAT UNSAT proves absence
only within the declared support, grammar, constraints and gate bound; timeout
does not prove absence. This study remains a proposal for user decision.

Additional primary references:

- [On-the-fly and DAG-aware: Rewriting Boolean Networks with Exact Synthesis, DATE 2019](https://people.eecs.berkeley.edu/~alanmi/publications/2019/date19_rwr.pdf): bounded resynthesis, don't-cares and graph-context costs.
- [Exact DAG-Aware Rewriting, DATE 2020](https://people.eecs.berkeley.edu/~alanmi/publications/2020/date20_rwr.pdf): structural decomposition with SAT on small prime remainders and multiple realizations; its experiments leave don't-care exploitation to future work.
- [SAT-Based Exact Synthesis: Encodings, Topology Families, and Parallelism, TCAD 2020](https://people.eecs.berkeley.edu/~alanmi/publications/2020/tcad20_exact.pdf): bounded topology/function encodings and search-family tradeoffs.
- [Author's resubstitution engines](https://github.com/alanminko/resub): exact synthesis with side divisors and Boolean relations; per-pattern Boolean relations must not be conflated with temporal cross-pattern clauses.

## Review of three completed construction studies (2026-09-15)

This review reads completed task records, source changes, raw CSVs and existing
independent audit records. No optimization, build, new task or algorithm change
was launched. At this review point production remained
`89858c9e93c1ccde6b06f42b62909fde12c57d09`; only this report was updated.
Research branches were then separate prototypes:

- Output alignment / SAT-core feedback: task
  `01a09e87-3745-7540-aa19-a5a9e29026a6`, tree `abc-relobs-20260914`,
  HEAD `e3c16c846a1094cd2a1c1e072d77ba1a589db6ae`. Measured core binary is
  frozen from `dc2968562`; final HEAD also fixes the separate native-cost pilot.
- Relational SAT construction: task `01a0a0bd-6c56-7820-bf5f-b99a63239f34`,
  tree `abc-output-relconstruct-20260914`, HEAD
  `ada929b568d284c9a9fc9ae5a00f7ddb6d5840c9`.
- Cut/DAG-cost construction: task `01a0a0be-5319-7e20-a2ae-d9574b0bbdff`,
  tree `abc-cut-dagconstruct-20260914`, HEAD
  `e390a2e1a3658eda655619021d83db976fe0f0de`.

Mode numbers are branch-local: R23 has a different meaning in each tree.
Do not reproduce a result using a mode number without its binary identity.

### Coverage and comparable quality

All three tasks attempted full fast35 primary families at 1800 seconds per
ABC call. Full attempt coverage is not full verified quality coverage:

| construction arm | primary optimization PASS / TIMEOUT | independently verified primary products |
|---|---:|---:|
| SAT-core native | 26 / 9 | 26 |
| relational SAT, uncapped tail | 12 / 23 | 12 |
| relational SAT, 32-model tail cap | 22 / 13 | 22 |
| multiple structural cuts and cost handling | 27 / 8 | 27 |

Relational SAT's 22 include one independently proved full-miter PDR result
after raw DSEC UNKNOWN. Cut's 27 likewise include a separately discharged
raw DSEC UNKNOWN. SAT's single 3600-second retry adds three equal verified
products (25 total, still +17 AND); cut's retry adds no R27 product. Core did
not retry. No missing final product receives quality credit.

Primary published pairs: core versus old R11 output saves 27 AND on 25
products (12/13/0 better/equal/worse), but versus window leaves eight MORE AND
on 23 (5/13/5). Cut versus its R21 cone control saves 96 on 27 (11/16/0).
Relational SAT versus its R21 control saves 17 on 22 (7/14/1). These are
different controls/populations and must not be ranked directly.

This review independently joined the primary integrated CSVs by file/input
SHA. The two new tasks' R21 controls have identical final AND on all 27
common completed inputs. Relative to this shared R21 control, core saves
23 AND on its 26 completed products (10/16/0). Restricting ALL three methods
to their SAME 22 independently verified inputs gives:

| candidate versus shared R21 | additional AND reduction | better / equal / worse |
|---|---:|---:|
| cut/DAG-cost | 19 | 7 / 15 / 0 |
| relational SAT cap32 | 17 | 7 / 14 / 1 |
| SAT-core native | 15 | 8 / 14 / 0 |

All paired latches are unchanged. This subset excludes sasc and other timeout
cases, so it establishes comparable modest increments, not whole-fast35
dominance. Runtime comparisons should retain each experiment's own control,
not mix timing from separately scheduled controls. Original paired mean/median
pipeline ratios are cut 1.049880/1.000492, relational SAT 14.123117/1.057788,
and core versus old output 2.184412/1.884694. Timing includes common prefixes
and research diagnostics and excludes timeout cost in these paired ratios.

### What was implemented, and what remains untested

1. Core feedback proves a smaller necessary failed-trace clause using a fixed
   real PI trace, abstract per-frame root values and pattern-guarded assumptions
   applying at every frame. SAT chooses no recipe topology. On 710 matched
   initial roots, units grow 608 -> 19,866 and branches fall
   136,690 -> 68,337. The constructor still branches into ON/OFF assignments.
   Thus it improves information but does not implement relation-preserving
   native expression decomposition. Of 3,720 PDR-valid candidates on the
   audited 26 products, 3,638 have nonpositive actual gain and retain MFFC
   nodes; 60 become positive Build commits. This is a concrete area-objective
   problem, not evidence that correctness freedom is exhausted.

2. Relational SAT directly encodes cross-pattern clauses and a shared AND DAG,
   but runs only after the old search hits its branch cap, with remaining
   proposal budget and MFFC > 3. Its preferred R25 limits SAT models to 32
   over the ENTIRE tail, across roots and snapshots. It retains the old raw
   MFFC-1 gate bound, uses greedy soft old-root-value preferences and returns
   the first proved positive candidate. It does not yet test a primary,
   area-directed relational constructor. The b05_opt witness beats a doubled
   old branch cap; that excludes this specific effort control, not every
   explanation based on larger/differently allocated search effort. The
   22-case SAT statistics include 56,345 preference queries and 4,393.974
   seconds attributed to relational synthesis; runtime cannot be attributed
   solely to downstream whole-product verification.

3. Cut construction adds legal frontiers of at most four leaves, computes
   complete strict truth tables and asks Kit/BDC for realizations. It runs
   only after native produces no accepted edit, then compares those cut
   realizations using frozen-DAG gain. It neither changes the native partial
   expression objective nor jointly synthesizes temporal care completions.
   The independent SAT adapter receives cut leaves/truth, not a portfolio of
   known side-divisor functions with their retention costs. Structural reuse
   is priced after synthesis. These are narrower capabilities than the
   broader support-and-DAG-cost research question.

4. Cut R21 -> R23 gives +9 AND, followed by +87 from R23 -> R27, including
   +70 on sasc. Source and raw counters further qualify the first label:
   R23 leaves the native raw iterator unchanged, records 174,260 cost
   evaluations but ZERO old-bound exclusions/rejections, and permits 11
   zero-new native commits. Its behavioral change is primarily acceptance
   of zero-new-node recipes and the resulting paths, not a demonstrated
   improvement in native DAG search. Ordered Build attribution includes
   these generated recipes; it does not imply physically new logic for every
   counted edit. The separate cut lane does establish raw-bound-excluded,
   positive actual-gain witnesses.

5. Exact cut mode explicitly skips cuts unless Kit/BDC already found positive
   actual gain (`Ctor == 2 && !CutHadPositive`). The 35-function offline
   optimum sweep also comes only from positive candidate logs. Its zero
   additional commits therefore does not test the central exact-only question
   of cuts where the old constructors fail to find any profitable realization.
   Thirty-two sampled functions are already raw-gate optimal; three improve
   by one raw gate without a selected gain. This supports only that narrow
   completion result, not a broad conclusion against exact construction.

6. Old small-cut gains arose after a weaker 18,697-AND baseline. The current
   experiments follow stronger CEX/ODC and an output-Direct prefix and have
   incomplete, different populations. No matched experiment allocates all
   historical loss of gain to CEX versus Direct versus changed search. The
   current standalone rewrite residual nevertheless falls from 108 after
   R21 to 30 after R27 on the same 27 products; this is evidence of diminished
   conventional local opportunity in that population, not a global ceiling.

### Research-process interpretation

The tasks produced code, real local witnesses and full batch attempts. They
did not establish broad full-fast35 quality or exhaust the proposed methods.
The two new tasks were deliberately isolated from the concurrently improved
core feedback, so no evidence yet measures their composition. Gains cannot
be added. Several remaining timeouts precede the new Build tail: the core
audit counts five inside Build, one after the Direct prefix without a root
log, and three without a tail log. A 1800-second whole invocation can censor
the new constructor through unchanged prefix work.

A better next decision would distinguish the tested cheap/local cut lane from
the untested exact-only and relation-plus-area questions. For a future study,
measure candidate mechanisms on identical independently verified frozen
snapshots, then separately validate transfer through the complete flow. This
is experimental isolation, not a proposed production cache optimization.
Changes to the accepted timeout/coverage policy or new algorithms still need
user authorization. No such follow-on is started by this review.

Evidence authorities for this review:

- `script2/evidence/stran2_output_alignment/20260914/{metrics.json,core_noop_audit.json,timeout_stages.json,core_window_divergence.json}`
- `script2/evidence/output_relconstruct/20260914_relconstruct_v1/{analysis_r25_pdr22.json,analysis_r25_extended_pdr25.json,manifest.json}`
- `script2/evidence/cut_dagconstruct/20260914_round1/{primary_r21_vs_r27_v1.json,primary_r23_vs_r27_v1.json,twoexact_complete_r27_v3.json}`
- Cross-task joins use `experiment_reports/20260914_cut_dagconstruct_baseline_repro/stran_current_stran2.csv`,
  `20260914_cut_dagconstruct_multicut_r27_v3/stran2_r27.csv`,
  `20260914_output_relconstruct_v1/{baseline_r21,candidate_r25_cap32}/stran_current_stran2.csv`,
  and `20260914_stran2_output_alignment/core/stran_current_stran2.csv`.
  All paths above are relative to `/mnt/home/zhaoxiran/` or, for experiment
  family names after the first, its `script2/experiment_reports/` directory.

## Scientist-directed next round (2026-09-15)

The user explicitly authorized the scientist to message and continue the three
existing tasks above, to stop low-value implementations and continue promising
mechanism-based work. All three coordination messages were accepted and their
new turns were confirmed in progress at 2026-09-15 03:09:56 UTC. No production
algorithm or binary was changed and no new task was created.

**Superseding user instruction (2026-09-15):** the user has already continued
the tasks and explicitly suspended quota management until they ask for it
again. Do not query or wait for account-usage readings, impose percentage
thresholds, or pause research because of quota accounting. The initial shared
ten-point / 46%-54%-56% coordination policy is withdrawn. This override was
delivered to all three active tasks. Continue or conclude work according to
research value and evidence. Each task retains a maximum of 16 active compute
workers/threads, and the project-wide cap remains 200.

Assigned questions:

- **Cut/DAG-cost:** test the exact-only region where Kit/BDC fails to produce
  positive actual gain; census negative as well as positive cut populations.
  Study legal side functions and retention costs only when a matched witness
  supports the mechanism. Do not mistake the old zero-new acceptance change
  for area-directed native search, or repeat positive-only optimum sweeps as
  evidence against the entire direction.
- **Relational SAT:** compare direct relational construction on frozen roots
  without the old fail-only/MFFC>3/global32 screening bias. Isolate soft
  root-value preferences and search effort, then study actual-gain-directed
  structure selection. Keep support selection fixed and distinguish synthesis,
  preference and proof costs. Frozen core feedback may be used only as a
  separately attributed input; native relational recursion belongs to the
  output task.
- **Output/native:** derive and implement exact residual-relation propagation
  through AND/inverter decomposition with fixed support and core clauses;
  verify the algebra on exhaustive small instances. Introduce real retained
  support information into construction when supported by a witness. Match
  constructors for window/output comparisons; avoid further raw-N expansion
  or circuit-specific repairs as the default route.

Each task first completes one coherent discriminating stage, then continues
within its scope/budget only when the evidence supports useful transferable
quality. Frozen independently verified snapshots separate constructor testing
from expensive unchanged prefixes; full-flow transfer is measured separately.
Timeout remains 1800 seconds per ABC/final audit, with at most one justified
3600-second timeout-only retry. Missing snapshots and products remain explicit.
Whole-output proof, reset/interface integrity, current-graph validation and
positive exact cleanup gain remain mandatory.

Tasks keep their own worktrees and dated evidence namespaces, edit only their
own research report, and send the scientist one concise result at a completed
stage or genuine blocker. They do not message each other, create extra tasks,
merge production, enable defaults or launch Quick268. Context should be reduced
to verified state and the current bounded question; a task that cannot continue
reliably with its current context should report that at the next boundary.

### Completed stage: residual-relation native construction (2026-09-15)

The output task completed an offline Python constructor on its private
`e3c16c846a1094cd2a1c1e072d77ba1a589db6ae` base. No production C code,
optimizer binary, online commit, or new Fast35 run was produced. The scientist
audited the implementation and recomputed the primary paired CSV, then accepted
stopping this restricted enumerator's online integration. The broader
relation-native/output ODC question remains open; no follow-on was launched.

For a fixed actual operand expression, substitution through
`h = (a AND g) XOR p` is exact: a clause literal `h(x)=v` becomes the constant
`p=v` when `a(x)=0`, or `g(x)=v XOR p` when `a(x)=1`. This preserves the frozen
relation, which is still only a necessary condition for temporal correctness.
The chain grammar fixes one literal operand at every AND. A separate balanced
control adds a fixed one-AND operand paired with a one-AND remainder at three
gates. This is not general DAG construction or SAT topology synthesis.

The authoritative `ordered710` comparison uses 710 roots from 25 independently
proved Direct snapshots, identical pools/core clauses and gate bounds
`min(3, MFFC-1)`, at most 320 proposals and 320,000 primitive work visits.
The adapter first partitions clauses into ON/OFF assignments, preserving the
original clause and term order, then uses the same restricted grammar. All
2,840 rows and paired snapshot/pool/pattern/clause/MFFC/bound identities match.

| Grammar | Adapter positive roots / separate gain | Residual positive roots / separate gain | Root gain better/equal/worse |
| --- | ---: | ---: | ---: |
| Chain | 6 / 8 | 7 / 9 | 1 / 709 / 0 |
| Balanced | 6 / 8 | 8 / 10 | 2 / 708 / 0 |

These gains are independent local replacements, not additive whole-circuit
QoR. Earlier canonical-order differences of +4/+5 were withdrawn because
sorting changed the adapter's bounded branch order. Only the original-order
results above are primary. The old full native constructor had 15 positive
roots in this population; balanced residual matches six, misses nine and
adds two. Its restricted gate/shape/work envelope is not a replacement for
the existing native search.

The sole newly found relation-construction/state-fork witness relative to the
frozen legacy core is ethernet root 264: two new ANDs, exact gain one,
independent permanent DSEC PASS, and replayed root/state counterexamples. It
directly drives RI26 without AND fanout, so the same witness also refutes the
corresponding exact-window equality. Here the adapter generated zero proposals
at the work limit while residual generated 320 (winner number 36); this does
not isolate expression freedom from finite-budget search efficiency. The
additional balanced root b07/55 was already found by the old native. Sasc/763
is root/state equal and found by both controls, so its difference from legacy
belongs to grammar/order rather than state freedom.

Important untested mechanisms remain: new proof CEX were not fed back into
construction after the frozen core; cost was evaluated on complete recipes,
not used as a sound partial-retention search bound; general compound operands
and DAG sharing were not covered. Many generated candidates were rejected by
real trace replay. Consequently neither larger raw-N nor deeper literal chains
is justified by this stage, and it does not measure a closed-loop constructor.

Validation includes 45,240 exact substitution checks, 3,321 exhaustive
two-clause instances, balanced checks covering all 16 two-variable Boolean
functions, and 35 Python regressions passing with three skips. Across the
construction and validation stages, 149 new independent DSEC calls returned
10 PASS / 139 explicit counterexamples / zero unknown or timeout; identical
permanent product hashes reused certificates. These are proof-call counts,
not online commits. No optimizer/build/proof jobs remained at delivery.

Primary raw:
`/mnt/home/zhaoxiran/script2/experiment_reports/20260915_round2_relobs_residual_0315/ordered710_construction.csv`.
Evidence:
`/mnt/home/zhaoxiran/script2/evidence/20260915_round2_relobs_residual_0315`,
including `ordered710-results.json`, `control-order-correction.json`,
`final-audit.json`, and `ethernet-state-fork/`.
Authoritative source freeze `frozen-final-v2` source archive SHA256
`d11bf639ee802d42b267bd67573acfdad1534e4164f4d6f6ead8418d1948c6d2`,
patch SHA256
`3659d76a187c63f1a5dbf5b9334ba4effe918218768a0df1d7e956436c83aab5`.
Preserve the verified algebra and witness; consider reuse only after the other
two tasks report their complete discriminating stages.

### Completed stage: exact-only strict cuts and side-divisor audit (2026-09-15)

The cut task completed its second stage on private report/source commit
`26582c4e321b4cc19331df2dce50f548d6567afb`; authoritative documentation and
metadata corrections are commit `01efff16216329ce37e79d3da4231244e9be02f4`,
with no new computation or algorithm changes. Its exact commit implementation is
`d45460067b80b020d6ce2a929131b6fe1a408e1e`; the side audit implementation is
`60d7f55f14ae9315169a3e2d28d7295ae3c7e528`. The scientist verified report
hashes, paired frozen input identities, final counts, proof status, common-case
overlap and R27 tail timing. Accept the stage closure: keep exact-only as a
private opt-in research candidate and stop the current side-divisor add-on
restricted to leaf-exact-positive views. No production integration, default enablement or follow-on
experiment is authorized by this result.

The R6 Direct prefix attempted Fast35 and produced 31 independently verified
snapshots; b12, b12_opt, i2c and steppermotordrive timed out before a product.
All 49,388 retained legal structural cut views of at most four leaves were
audited, including the Kit/BDC nonpositive population. Kit/BDC had 242 positive,
49,146 nonpositive and zero unconstructible views. Exact AND/inverter DAG
synthesis made 6,138 unique calls plus 43,250 cache hits, all OPTIMAL with no
UNKNOWN or over-N result (N20, 100,000 conflicts per unique truth, q320 frontier).
Optimality here concerns the raw gate objective, not current-graph area cost.

The `exact-improved=3918` counter means **actual evaluated gain exceeds the
best Kit/BDC gain**, as implemented by `Gain > BestGain`; it does not count
raw-gate reductions. The initial private report's raw-recipe wording was
corrected in the authoritative metadata without rerunning experiments. Exact yielded
219 positive views: 199 previously positive and 20 previously nonpositive,
the latter in eight cases. Thus a raw-optimal representative can lose actual
positive gain on 43 of the 242 old-positive views; it is not a dominating
replacement for existing graph-aware construction.

| Frozen input population | Final AND before -> after exact-only | Added reduction / control final AND | Better/equal/worse | Independent final DSEC |
| --- | ---: | ---: | ---: | ---: |
| R6 Direct, 31 products | 12,421 -> 12,412 | 9 / 0.072458% | 8/23/0 | 31/31 PASS |
| R27, 27 products | 4,004 -> 4,003 | 1 / 0.024975% | 1/26/0 | 27/27 PASS |

Latches are unchanged (1,387 and 967 respectively). Positive generated
views/proved winners/commits are 20/8/8 after R6 and 1/1/1 after R27. The
diagnostic invokes `&stran_cut_exact_one` once per snapshot, committing at most
one winner per circuit; this is not an iterative pass to a fixed point. On
the common 27 cases, the R6 exact wins sum to five AND and R27 already absorbs
four; b11 retains the one-AND opportunity. The other four R6 ANDs occur among
R27's unfinished cases and have unknown transfer. Common-27 R21 -> R27 ->
exact is 4,100 -> 4,004 -> 4,003: 96 then one additional AND, or 2.341463%
then 2.365854% reduction relative to R21 final AND, not source-normalized
Fast35 reduction. Exact tails do not emit standard Ordered Seq counters and
must not be silently added to the frozen prefix's Build attribution.

The concrete cost witness is b10 root 91. Kit/BDC and exact both use three
raw gates, but structural hashing gives three versus one physically new
nodes, changing exact gain from -1 to +1. This supports studying construction
with actual new/retained-node cost; it is not evidence that simply minimizing
raw gate count is sufficient.

The side audit requires each side divisor to precede the root and depend
solely on the structural cut leaves. It evaluates recipes on those original
variables to preserve correlation, and charges physical new nodes and
retained MFFC cost. It exhausts the 0/1/2-AND recipe grammar for the selected
side set, with no side truncation on the audited positive views. On R6 the
best side versus leaf-only exact results are 0/8/12/0
better/equal/worse/no-implementation; R27 has 0/0/1/0, both zero additional gain.
**Population limitation:** source skips `LeafGain <= 0` before side search.
Only the 20 R6 and one R27 leaf-exact-positive views receive side enumeration;
49,146 and 11,757 are eligible census counts, not exhaustive side searches.
The region where leaf-only exact remains nonpositive but a side construction
could become positive is untested. This stop decision applies to the current
restricted experiment, not to all side-divisor/DAG synthesis.

Timing uses frozen prefixes plus measured tails. R27 versus R21 has pipeline
ratio-of-sums 1.010480 and total ratio-of-sums 1.005426. The R27 exact tail
takes 29.49 seconds, plus 3.37 seconds independent DSEC; its additive pipeline
and total ratios are 1.004009 and 1.004062. Sequential composition gives
approximately +1.4531% pipeline and +0.9510% total over R21, not a fresh
integrated timing run. Per-case R27 tail pipeline ratio mean/median is
1.359449/1.017127, so the small aggregate overhead should not imply uniformly
small case overhead. R6's exact tail takes 86.48 seconds. Side audits are
diagnostic costs excluded from candidate flow time.

The stage does not cover complete Fast35 QoR (31/35 R6, 27/35 R27), larger
cuts, other frontier choices, retained-cost topology optimization, or temporal
ODC truth completion. Preserve the b10 cost witness and exact-only evidence
while awaiting the remaining relational SAT stage; do not expand a new search
solely from the untested-space list.

Evidence summary:
`/mnt/home/zhaoxiran/script2/evidence/cut_dagconstruct/20260915_round2_summary_r1/summary.json`
(corrected and verified SHA256
`d7c4384bb9d7ce441459d68e1d5b3c11938f8ea2798e8d152575c6ba860f6e3c`).
Primary exact-tail CSVs are
`/mnt/home/zhaoxiran/script2/experiment_reports/20260915_cut_dagconstruct_exactonly_prefix_v1/cases.csv`
(SHA256 `a860886da7b0a792d8d858af0852f4511d5095b24b97e897d76fec4bbac38a34`)
and
`/mnt/home/zhaoxiran/script2/experiment_reports/20260915_cut_dagconstruct_exactonly_after_r27_v1/cases.csv`
(SHA256 `c54e9030c6f29b5535e1fb19683a3393935d13f0635bdf5814064f19c9799db9`).
Their frozen exact binary SHA256 is
`c8f932f9a05c2002ef3d578c47ab7a4d09bb526ab370f93f0950deceb85ad5fd`;
side binary SHA256 is
`c09e53916b482f20bd7be8295a07957dd61616426cd7a8136015e7a6e602b4a3`.

### Completed stage: relational SAT with behavioral preferences (2026-09-15)

The relational SAT task completed source commit
`786466ac28b4487190ab30f911995d6573f1e549`, with corrected authoritative report
commit `19adf2bf039e8cbf49094f1599eafbecdc454a1b`, in its private worktree. The
scientist verified primary artifact hashes, paired input identities, final
metrics, diagnostic logs and constructor/selection code. Keep this as a
research prototype without default enablement. The user stopped the separate
3600-second timeout retry: zero completed cases, no quality overlay, and no
active experiment remains. All three round-two experimental stages are now
closed; metadata clarification does not authorize new computation.

The constructor encodes learned cross-observation clauses directly over a
shared AND/inverter DAG, with 1--20 gate families. R33/R35 attempt one model
from each family per root visit. Each SAT model is sought with minimum
Hamming disagreement against the old root's majority value on each projected
observation row, subject to the relation and bounded SAT effort. A unary
totalizer encodes cardinality bounds. This is a soft search preference, not a
proof obligation or guaranteed optimum when the optimization query is UNKNOWN.

Exact frozen-graph killed/new-node gain is evaluated **after** a complete
structural model is generated. Positive models are ranked by gain, at most
five candidates are checked, and the best proved positive cleanup gain is
committed before refreshing the graph. Thus actual area directs the proof
queue/selection; retained-node cost is not the SAT topology objective.
Refutations supply first-difference relation clauses and filter remaining
candidates. The selected single-sweep arm does not regenerate models on that
root within the same call after learning those clauses. Neither a single
sweep nor five checks establishes structural exhaustiveness.

The matched diagnostic starts from the same 52-AND/34-latch b05_opt Direct
snapshot, root pools and learned initial relations:

- With the same DAG grammar and 7,040 models, direct relation encoding yields
  800 positive structures versus 559 for a fixed completion (+43.1%). These
  are different sampled structures, not identical DAGs; neither frozen arm
  finds a formally valid replacement. With iterative CEGIS, direct relations
  find five valid structures on two roots, while recomputing one deterministic
  completion finds none, again at 7,040 models. This tests one completion
  policy, not all possible completions.
- At initial root 67, relation fingerprint `0e6892537071dd3f`, 48 clauses,
  130 rows and 23 materials match exactly. Both arms have six positive
  structures and five checks: Hamming proves two (best gain three), no
  preference proves zero. Hamming returns 19 models versus 20 without
  preference because its 20-gate query is UNKNOWN. The corrected report
  explicitly distinguishes a family attempt from a returned model.
- Across the snapshot, Hamming R35 obtains five commits/gain nine from 599
  models and 57 checks; repeated no-preference R34 obtains one commit/gain
  two from 10,560 models and 1,266 checks. This excludes an explanation based
  only on more candidates/checks, not greater SAT computational effort.
  R35 takes 891.90 seconds versus R38 single-sweep no-preference at 9.52.

Full-flow b05_opt confirms 50 -> 43 final AND, unchanged Direct stream and
latches, at 279.374 -> 1,171.005 seconds optimization (4.192x). Full Fast35
primary candidate attempts all 35 at 1800 seconds: 27 complete and all 27
pass independent final DSEC, with eight optimization timeouts. Old R21 also
completes 27, but b11 is old-only and des_area new-only, leaving 26 common
verified products. All 35 available Direct commit streams match. No missing
product or interrupted retry receives quality credit.

| Common verified population n=26 | R21 | R33 | Change |
| --- | ---: | ---: | ---: |
| Final AND | 3,758 | 3,719 | -39; 11/11/4 better/equal/worse |
| Latches | 937 | 937 | 0 |
| Ordered Seq Build | 1,143 | 1,182 | +39 |
| Total SEQ | 2,900 | 2,939 | +39 |
| Direct gain | 1,688 | 1,688 | 0 |
| Experimental tail commits / gain | 40 / 46 | 63 / 85 | +23 / +39 |

Final reduction is 1.037786% of R21 final AND; Ordered Build and Total SEQ
increase 3.412073% and 1.344828% of their respective baseline gains. These
are different denominators, not percentage-point improvements in full-Fast35
source-normalized reduction. The four regressions lose one AND on b04_opt,
one on b09_opt, three on b10 and one on b10_opt. Gross improvements sum to
45 AND and regressions six. Ordinary pre-tail generated/proved/selected
counters are identical; experimental-tail models/checks are separate counters.

The candidate tail has 74,081 unique models, 14,490 positive-cost models,
7,426 checks, 74 PASS and 63 commits, including five zero-new-node commits.
The scientist's log audit finds 74,100 structural family queries with 339,308
Hamming-bound queries; family statuses are 74,081 SAT / 18 UNSAT / one
UNKNOWN, and 44 searches report unresolved Hamming optimality. Feasible models
under an unresolved preference bound still require successful whole-output
proof; no optimality claim follows from their final equivalence.

Paired optimization sums are 6,191.085 -> 13,543.059 seconds, ratio 2.187510
(+118.75%), with per-case mean/median ratios 11.764251/3.116125. Including
runner DSEC, sums are 6,947.763 -> 14,282.070 seconds, ratio 2.055636. These
historical one-shot timings show a substantial cost, not a controlled speed
benchmark. Additional independent audit time is not included in runner DSEC.

The scientist additionally classified existing tail commit logs by old-root,
window and state proof status, where one denotes PASS and zero refutation:

| Commit proof class (root/window/state) | R21 commits / gain | R33 commits / gain |
| --- | ---: | ---: |
| 1/1/1: root equality proved | 26 / 30 | 52 / 69 |
| 0/1/1: window/state preserved | 6 / 6 | 4 / 5 |
| 0/0/0: output-only, state changes | 8 / 10 | 7 / 11 |

The net +39 appears in the root-equality category; the other categories'
combined gain stays 16. This is commit classification on diverged graph
trajectories, not a matched causal ablation. It supports investigating better
equivalent-function construction and useful behavioral preference, rather
than attributing this whole increment to newly released ODC state freedom.

Evidence:
`/mnt/home/zhaoxiran/script2/evidence/output_relconstruct/20260915_round2_v1/manifest.json`,
corrected and verified SHA256
`168ca50e215b4ae9ccdee0ee6824fa544c56b8c1b100adb45974a6fd27b52ae1`.
Primary candidate CSV:
`/mnt/home/zhaoxiran/script2/experiment_reports/20260915_output_relconstruct_round2_v1/candidate_r33_sweep1/stran_current_stran2.csv`,
SHA256 `a7e0ee097ddaaf73c0a7d0cace179004935867c8b9972cbe0eca08778f752c24`.
Frozen measured binary SHA256
`7004e1b7d4ade4f08d01f875382ba1cff7e56661e95e8e6768fa28a1cea017e2`;
separate final-source validation binary SHA256
`cb32348f8d8c5837cce675ccf598ca68ce1638e024fd472da5a6f5cd5225d5cb`.
The independent checker is production validation binary `a19f03dd...`.
Diagnostic scope, optimality and commit-class attribution wording has been
corrected in the authoritative report/manifest, without new optimization,
build or proof runs. Raw results remain unchanged.

### Joint interpretation after the three completed stages

Do not compare cut's 27-case gain of 96 directly with SAT's 26-case gain of
39. On identical source hashes and the shared R21 control for the SAME 26
verified products, R21 final AND totals 3,758, cut R27 totals 3,665 (gain 93,
10/16/0), and SAT R33 totals 3,719 (gain 39, 11/11/4). Cut and SAT each beat
the other on eight cases and tie on ten. Cut's 70-AND sasc improvement drives
much of its aggregate lead; SAT has distinct wins on b05, b07, b08 and related
optimized variants. Per-case incremental gain/source means are 0.400465 and
0.412352 percentage points, respectively, with median zero for both.
These results show complementary final products, not additive gains or a
measured combined algorithm. No online composition was run.

The residual-native stage remains an offline grammar-limited result and has
no new full-flow metric to place in this table. Its verified clause-substitution
algebra is reusable evidence, not a demonstrated online quality improvement.
Cut exact-only closes a small measured gap after R27; positive-leaf side
add-ons add none in their restricted population. Relational SAT provides the
clearest new controlled evidence for behavioral preference, with substantial
time cost and incomplete coverage. Directly guiding topology generation with
actual retained/new-node cost remains untested by all three implementations.
This is a candidate question for discussion, not authorization to start a
fourth experiment, combine branches or continue the stopped retry.

## Consolidation review and proposed speed focus (2026-09-16)

This section records the read-only consolidation review made before the later
integration authorization. At that review point production was
`89858c9e93c1ccde6b06f42b62909fde12c57d09` and only this report was modified.
The subsequent authorized implementation, validation and cleanup superseding
that pre-integration state are recorded below.

### Production versus research inventory

Verified production ancestry already includes tight-budget template/residual
coverage repair `8c202f285`, TFO/complete-information ODC baseline `3836f6091`,
ODC auxiliary signatures `f4fbe6631`, reachable strict-CEX teaching `e29304187`,
strict signature/empty-label improvement `e1d5a95d5`, and integrated F/C
handling `55e476c65`, followed by consolidation and module refactoring.
These do not need to be merged again. The measured Fast35 F2/C1000 window-ODC
quality reference remains 17,393 final AND, mean Ordered Build/source
9.599563% and Total SEQ/source 10.242455%, with 35 independently verified
products. These are separate metrics, not one overall reduction percentage.

Output-proof research `cc295e594`, cut/DAG construction `dbc2048d6`, relational
SAT `786466ac2`, and net-gain construction `d031b37af` are not ancestors of
production. Their private trees include multiple experimental modes and
diagnostics; whole-branch merging is not equivalent to extracting a reviewed
production feature. Output proof must preserve shared PIs, reset, independent
states and permanent-product obligations; accepting root inequality never
means dropping the final equivalence obligation.

The largest recent unmerged quality result is output-Direct R6, not the latest
SAT constructor. Its original matched 31-product comparison is 14,380 ->
12,418 final AND (1,962 reduction), 28/3/0 better/equal/worse, unchanged
1,382 latches and unchanged Ordered Build. The 35 attempts have 31 independent
PASS and four optimization timeouts. Paired stran-stage sums are
2,053.935 -> 6,324.506 seconds (about 3.0792x); the relobs proof-time profile
is 3,337.738 seconds, including the prototype's proof/diagnostic accounting.
Source: `evidence/stran2_relbuild/20260914/metrics.json`,
`verified_comparisons["control/direct_only"]`. This is a distinct frozen
experiment from the later R6 census totaling 12,421 AND / 1,387 latches;
do not splice those baselines together. It is also not a complete-Fast35
speed or coverage guarantee.

### Newly completed net-gain construction

The task `实现净收益驱动的候选构造` completed in private tree
`/mnt/home/zhaoxiran/abc-netgain-construct-20260916`, branch
`codex/netgain-construct-20260916`. Measured algorithm commit is
`d031b37afc620d5aa36bf21aa7399c3f732826d9`; final review commit is
`7bfb48dcdc67d63a4cf9f78b6f7bf3f3d7546056`. The scientist checked the report,
source cost/bound interfaces, manifest entries, primary CSV and aggregate
arithmetic. This stage supersedes the September 15 statement that all three
implementations left cost-guided topology generation untested.

Canonical live physical AND nodes and shared Boolean retention variables now
put the union of retained MFFC nodes into SAT cardinality constraints. For a
fixed gate family, B minimizes retention before returning its candidate. A
uses the same material/grammar but returns an unconstrained model, then
evaluates cost. An extra-query control E tests the query-allowance explanation.
The full-care function is identical in all arms, so Hamming is inapplicable.
On fixed R27 snapshots, B recovers 12 A-nonpositive views and improves seven
best positive root gains. Eleven positive-view advantages remain versus E;
E matches permitted query counts, not conflicts or time. B takes about 5.694x
E's conflicts and 16.5x its SAT wall time.

| Same 27 verified R27 snapshots | C: R27 | A: posterior-cost control | B: cost-guided generation |
| --- | ---: | ---: | ---: |
| Final AND | 4,004 | 3,969 | 3,965 |
| Latches | 967 | 967 | 967 |
| Added final reduction | 0 | 35 | 39 |
| Tail selected / gain | -- | 28 / 35 | 32 / 39 |
| Tail optimization seconds | -- | 88.315 | 155.014 |
| Tail SAT seconds | -- | 2.394 | 60.814 |
| Tail internal proof seconds | -- | 67.477 | 74.453 |

A->B is four AND on four circuits, 4/23/0, or 0.100781% of A's final AND.
C->A includes expanded material/grammar, a q320 frontier and fixed-point
regeneration, not just a single isolated mechanism. Do not attribute all 39
AND to the cost objective. B/A tail time is 1.755239x; both tails have 27/27
independent DSEC PASS. Their different commit trajectories explain why summed
retention may grow even when matched-family retention improves.

Fresh R27+B Fast35 attempts all 35 and independently verifies 27 completed
products; eight timeout in the unchanged R27 prefix before any netgain tail
starts. Every completed fresh prefix and final structure matches its frozen
counterpart, with writer-comment-only file-hash differences documented.
Source hashes pair across all 35. Final AND is 4,004 -> 3,965, 14/13/0,
with unchanged latches. On these same 27 cases R21 totals 4,100, so the
quality chain is R21 4,100 -> R27 4,004 -> A 3,969 -> B 3,965. This is not
the 26-case relational-SAT comparison population.

Historical R27 versus fresh R27+B completed optimization sums are
7,356.597 -> 7,470.667 seconds (+1.5506%); including independent DSEC they
are 8,070.180 -> 8,199.522 (+1.6027%). Different dates/load/checkers make these
descriptive, not a controlled overhead estimate. Eight timeout records have
missing exact times due to a runner time-file recording failure; original
attempts, interval bounds and CPU lower bounds remain explicit, with no retry
and no missing value counted as zero. Those calls account for about 14,344--
14,482 additional summed optimization seconds outside completed-case timing.

The quality boundary is explicit: local gain `|MFFC|-|retained union|-|new|`
does not capture every downstream cleanup merge. A verified combinational
example has local gain zero but total cleanup gain two (six AND -> four).
The positive-local-gain pruning excludes it. This is a completeness limitation,
not an observed incorrect transformation. No larger search is authorized.

Evidence manifest:
`/mnt/home/zhaoxiran/script2/evidence/netgain_construct/20260916_v1/evidence-manifest.json`,
SHA256 `c26469628f9c10d4249942b49453640075d043550c25a91c61726ba0bf015330`.
Measured binary SHA256
`75f0b455aaf4b455630c593f359520cee48752234fcdc9cc3f266a1cbe91c899`.
Primary raw:
`/mnt/home/zhaoxiran/script2/experiment_reports/20260916_netgain_construct_fast35_v1/candidate_B.csv`.
The frozen A/B results and complete source-to-product comparison are in
`analysis-final.json` under the evidence directory.

### Recommended consolidation decisions

- Retain current production strict/TFO/CEX/window-ODC behavior as the stable
  reference, with F2/C1000 as the already measured quality option. Do not
  globally increase F/C based on lower UNKNOWN counts or isolated final sums.
- First integration candidate: a clean, opt-in permanent output-proof Direct
  path and its correctness tests. It has the largest distinct measured quality
  benefit, but its current cost/coverage does not justify default enablement.
- Next candidate: R27's graph-costed multiple-cut construction in a separately
  identified quality path, once the output/trace dependencies are reviewed.
  Its 27-product gain is 96 over R21 at about +1.048% aggregate pipeline time;
  this is incremental tail cost, not the cost of output support over production.
- Retain netgain A as a secondary integration candidate: its frozen postpass
  captures 35 of B's 39 AND for lower cost. It still needs independent extraction
  and appropriate full-flow validation; do not call its package a proved single
  optimization. B remains an optional research ceiling, not the default target.
- Do not prioritize default integration of relational Hamming SAT, SAT-core
  native, residual <=3-AND enumeration, isolated exact-only, positive-leaf side
  add-ons, or the native-care/spatial window experiments. Their attributable
  increments, cost or coverage do not support that priority. Preserve evidence
  and negative-result scope rather than deleting research history.

### Proposed next focus: preserve measured quality while reducing work

Recent bounded construction changes have diminishing measured increments;
theoretical quality saturation is not established. Freeze the chosen quality
reference before a speed campaign. Separate lossless changes from deliberate
budget/quality tradeoffs, and report both coverage and timeout-inclusive cost.

Priority hypotheses, not launched implementations:

1. Measure required proof, classification-only root/window/state proofs,
   product construction and replay separately in the output prototype. Every
   accepted edit needs its actual correctness proof; optional diagnostic proofs
   must not be mistaken for unavoidable algorithm work. Current output checking
   rebuilds a product and invokes unbounded PDR per obligation; evaluate cheaper
   sufficient certificates, dependency slicing and sound incremental proof only
   with the same permanent-output guarantee and current-snapshot validity.
2. Attack old-prefix hard cases first. All eight latest timeouts occur before
   netgain starts. Optimize the responsible prefix phase based on profiling;
   making a small successful tail faster cannot recover that coverage.
3. Reduce unproductive Build and divisor selection work with sound feasibility,
   dominance or reusable exact information. Old dynamic-budget results do not
   authorize a hard no-hit or proof-gated cutoff: censored work can contain useful
   candidates, and current TFO/CEX/ODC behavior differs from the old experiments.
4. Report an optimization-only time/CPU metric separately from independent audit
   and research instrumentation, plus an all-attempt budget/coverage metric.
   Revalidate the selected quality reference on identical source hashes and
   explicit final proofs; candidate counts alone are not quality or speed.

## Production output/multi-cut integration and archive (2026-09-16)

The user subsequently authorized the reviewed output granularity and R27
multi-cut path for production integration, while keeping the stable default
and excluding the later SAT, residual, exact-only, positive-side and net-gain
prototypes. Code commit
`b9a3ee615fe1283f7a3a8c6c9f2c440755c5bbd3` is based on the preserved report
commit `3de8aa1401a53ff9d4a9c230638e7da321def0f9` and contains the maintained
implementation.

### Shipped interface and proof boundary

- Default behavior is unchanged: `nRelObs=0`, `fOutputProof=0`; no output tail
  runs unless requested. The parser accepts only `-R 0`, `-R 6` and `-R 27`.
  Modes 6 and 27 require the explicit `-Y 1` permanent-output opt-in.
- `-Y 1 -R 6` is the frozen Direct output-tail algorithm. `-Y 1 -R 27` first
  runs that identical Direct prefix, with no intervening scorr or cleanup, then
  runs temporal-cone construction with multiple legal structural cuts,
  Kit/BDC realization, frozen-DAG retained/new-node cost and current-graph
  exact cleanup-gain revalidation.
- Output commits prove the permanent external-PO product from zero reset with
  shared PIs and independent old/new states at every cycle. Root/window/state
  diagnostics are not accepted as substitutes. Assertions and replay remain
  active.
- `cecTranRelBuild.h`, its relation-SAT modes, residual hooks, one-/two-AND
  grammar experiments, R29 exact, side-divisor modes and net-gain construction
  were not imported. The production implementation is confined to
  `cecTranRelObs.h`, `cecTranTraceBuild.h`, their small shared interfaces and
  schema-stable profile parsing.

The explicit measured quality command is:

```text
-b 100 -S -1 -N 20 -B 16 -T 8 -D 1 -K 8 -Q 4 -W 8
-q 20 -j 5 -w 8 -V 0 -E 747118613 -d -k -J -O 0 -L 16
-H 2 -F 2 -C 1000 -Y 1 -R 27 -p
```

It uses the same eight `ABC_CEX_*`/`ABC_STRICT_*` environment settings shown
in the frozen R27 reproduction command. `-R 27` is an opt-in quality setting,
not a new default or a speed recommendation.

### Build, regression and default-path evidence

The clean full build `make ABC_USE_NO_READLINE=1 -j8` passed, followed by:

- `./abc -q '&stran_resub_test'`: PASS, including permanent-output Direct,
  temporal-cone, disjoint-clause, structural-cut and actual-DAG-cost self-tests.
- `test/run_stran_regression.sh ./abc`: PASS.
- `test/run_stran_microbatch_regression.sh ./abc`: PASS.
- `python3 -m unittest discover -s scripts -p 'test_*.py'`: 35 tests, 3
  skipped, PASS.
- `test/check_tracebuild_clause.py`: 54,272 function-trace checks, PASS;
  `test/check_tracebuild_cone.py`: complete-pool closure PASS.
- `test/run_stran_relobs_regression.py`: two small sequential products in
  modes 0/6/27, all equivalent, including divergent internal states.
- `git diff --check`: PASS.

For a direct default-path comparison, the exact pre-integration parent
`3de8aa140` was independently exported and built (binary SHA256
`4b046063d0b5a1740f6e235b230fef98c6c28e53342cb055b42df740b77bcee5`).
On Fast35 cases `001_b01` and `005_b03`, the full measured prefix with the
tail omitted produced byte-identical canonical AIGs before and after the
integration, independent DSEC passed 2/2, and the new output-tail log markers
did not execute. The comparison archive is `default_r0_compare.tar`, SHA256
`61feba93fe8c53f2dbc211d33c0a3f5527c50fab8d1ae8f8db6c6bacc1351cb8`.

### Integrated Fast35 result and timing scope

One Fast35 run used the exact frozen R27 parameters and environment, a uniform
1800-second limit per ABC invocation and 16 workers. No 3600-second retry or
Quick268 run was launched. The vanished temporary input directory was
recovered from the 35 frozen R27 normalized `base.aig` artifacts. Those files
are not byte-identical to the earlier raw input container, so their manifest is
`f14614fa9c61211fe3cc641fb64f7b1d25d3900ed67327fd71feec6eb3568407`,
not the old raw manifest
`8c410b9842675867e43acaedf66e59af69c84ad8176c37ae46702e94c4a5a9b7`;
before launching, the frozen independent
checker proved all 35 recovered files equivalent to the maintained benchmark
sources. The exact recovered set is retained in `recovered_inputs.tar`, SHA256
`d773b688bbf6fe10a9e85f7c1e0ea916d91a0df944fb58e73bd80b5566bf08b8`.

Optimization coverage is 27 PASS and 8 TIMEOUT. The timeout set is exactly
`b11_opt`, `b12`, `b12_opt`, `des_area`, `i2c`, `simple_spi`,
`steppermotordrive` and `systemcdes`; there are no optimization FAIL or UNKNOWN
records. Runner DSEC is 26 PASS, one `FAIL(0)`/undecided on `b13_opt`, and N/A
for the eight missing products. A separately frozen checker
(`abc-baseline-cc295e594`, SHA256
`2fe5213ea0823b9b18a47fdbec54dc3acd8181f01d365eb0a273a513cca6d26b`)
proves all 27 generated products, including `b13_opt`: independent DSEC is 27
PASS, 0 FAIL, 0 TIMEOUT, 0 UNKNOWN.

The effective common set is `b01`, `b01_opt`, `b02`, `b02_opt`, `b03`,
`b03_opt`, `b04`, `b04_opt`, `b05`, `b05_opt`, `b06`, `b06_opt`, `b07`,
`b07_opt`, `b08`, `b08_opt`, `b09`, `b09_opt`, `b10`, `b10_opt`, `b11`,
`b13`, `b13_opt`, `ethernet`, `sasc`, `ss_pcm` and `usb_phy`. Every one of
their canonical final AIGs and the compared stage/Direct/trace/multi-cut
metrics exactly matches the frozen R27 result.

On those 27 cases, the matched quality comparison remains R21 4,100 -> R27
4,004 final AND, +96 reduction, 11/16/0 better/equal/worse, with 967 latches
in both arms. The authoritative frozen same-run R27/R21 pipeline
ratio-of-sums is 1.010480. The fresh integration run has 7,298.432 seconds of
completed-case optimization and 21,701.813 seconds across all 35 attempts
including timeout walls. The historical R27 completed-case sum is 7,356.597
seconds, so fresh/historical is 0.992093; this cross-date, jobs-16 versus
jobs-2 observation is descriptive and is not a controlled speed claim. Do not
splice the output Direct result into the multi-cut delta: the separate frozen
R6 comparison remains 14,380 -> 12,418 on 31 common verified products, +1,962
AND, with optimization sums 2,053.935 -> 6,324.506 seconds (3.079x).

Raw evidence is under
`/mnt/home/zhaoxiran/script2/experiment_reports/20260916_stran2_output_multicut_integrated_fast35_v1`:

- integrated binary SHA256
  `414e6b790a768dbb1ab0707735cac5286fbba9f7bab236cd2b31c11dcbf09ca1`;
- CSV `stran2_r27_integrated.csv` SHA256
  `0599743443c6387e971cb41c9722e29a998ee0b8598b19147174c157cb47ce6e`;
- independent `summary.json` SHA256
  `60689499c3bddd0b371a4c26e2467f89625cf67e80d1b9191ea06a357aa8cd8d`.

### Archived research and final worktree state

The six completed research trees were archived at
`/mnt/home/zhaoxiran/script2/evidence/research_archives/20260916_stran2_consolidation_v1`.
`MANIFEST.txt` SHA256 is
`3fbe44d5dc708ff99308c4503a7bcd9d6227fd5a2622f96bc97108b4c24b0496`.
The complete six-ref recovery bundle SHA256 is
`5886fb01840d5c0dde4a4d2c04c2f221931ee45d96dfc7d086c0a795097946c8`;
`git bundle verify` passed and a fresh clone resolved every exact commit:

- output-relconstruct `19adf2bf039e8cbf49094f1599eafbecdc454a1b`;
- netgain-construct `7bfb48dcdc67d63a4cf9f78b6f7bf3f3d7546056`;
- relobs `e3c16c846a1094cd2a1c1e072d77ba1a589db6ae`;
- cut-dagconstruct `01efff16216329ce37e79d3da4231244e9be02f4`;
- odc-care `d8bbd0dd50c295d5fadc853960000241f48e51d7`;
- spatial-odc `d63431761d8ac1e2e803409467c575e3eee38d20`.

Each archive contains the exact tracked tree and STRAN2 snapshot. The dirty
relobs tree additionally contains a binary patch for its modified STRAN2 and a
tar of all five untracked `stran_residual*.py` scripts; the patch applies to
the recorded HEAD and extracted scripts byte-compare to the originals. Branch
refs and all pre-existing evidence/experiment reports remain. After verified
archival, the six authorized worktrees were removed with `git worktree remove`
and metadata was pruned. `git worktree list` now contains only production
`/mnt/home/zhaoxiran/abc`; no unrelated worktree was removed.

The next phase is speed analysis, not another quality search. Profile the
Build, divisor collection, cut enumeration, proof, selection, snapshot restart
and timeout-prefix costs separately before choosing a granularity. Preserve
the integrated quality reference and distinguish lossless engineering from
explicit budget/quality trades; this integration does not implement new speed
semantics.

## Validation and data

Required checks before changing the production branch:

```sh
make ABC_USE_NO_READLINE=1 -j8
./abc -q '&stran_resub_test'
test/run_stran_regression.sh ./abc
test/run_stran_microbatch_regression.sh ./abc
python3 -m unittest discover -s scripts -p 'test_*.py'
git diff --check
```

For any optimization change, retain before/after AIGs and run independent
whole-product DSEC with an explicit timeout. Report PASS, timeout, undecided
and parser failures separately; never impute missing cases.

Only the latest active result families are kept under
`/mnt/home/zhaoxiran/script2/experiment_reports`:

- `20260916_stran2_output_multicut_integrated_fast35_v1`: production
  output/multi-cut integration run and independent product audit
- `20260913_stran2_internal_scorr_*`: Fast35 F/C matrix
- `20260914_stran2_frame_quick268_*`: Quick268 frame attribution

Supporting launch records and audits:

- `/mnt/home/zhaoxiran/script2/evidence/stran2_scorr_fc/20260913`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_frame_attribution/20260914`
- `/mnt/home/zhaoxiran/script2/evidence/research_archives/20260916_stran2_consolidation_v1`

Do not add session handoff documents. Update this file only with a new complete,
reproducible result or a changed production invariant.

## Open questions

1. Can ODC proof depth be escalated per obligation without coupling F/C across
   initial scorr and every candidate?
2. Which observable multi-cycle signature predicts benefit after grouping by
   design rather than property file?
3. Can ODC search remain effective with a smaller B128/q320/L16 cost envelope?
4. Can auxiliary construction evidence preserve reachable-only recipes instead
   of conservatively excluding them?

Do not treat more proofs as monotone QoR: deeper F changes correspondence,
CEX, reduced graphs, ordering and committed snapshots under fixed budgets.
