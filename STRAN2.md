# &stran2: Current Goal And Results

## Review candidate: distinguish strict Build signatures and repair missing polarities (2026-09-12)

The continuation answers why TFO+CEX still missed useful native construction.
Owned tree: `/mnt/home/zhaoxiran/abc-strict-cex-refine`, branch
`codex/stran2-strict-cex-refine`, based on `e293041870452e7b36ea271692b450f169444921`.
Production remains unchanged at `3836f6091079664641bf42764b8a03c2310f6b54`.
This is an opt-in review candidate; the production default is not changed.
The earlier reachable-CEX release below remains the baseline, not the latest result.

**Result:** native strict Build reduction rises from **4.208656% to 7.057889%**,
and total SEQ reduction from **4.765709% to 7.696956%**, on all fast35 inputs.
Final AND sum falls from **19,444 to 18,319**, another **1,125 ANDs** removed;
21 circuits improve, 7 tie, and 7 regress. Latches remain 1,776 in both groups.
The cleaned release reproduces the complete prototype graph pairs for all
70 products (35 circuits, integrated and two-command flows). Fresh integrated
runtime ratio is **1.1371 mean / 1.0550 median** against the freshly rerun
TFO+CEX control. The earlier six-arm measurement was 1.1552 / 1.0788.
These are paired per-circuit pipeline ratios, excluding independent DSEC time;
shared-host single-run timing does not establish a precise small difference.

### Final ODC combination result and its limitation

The three-arm cleaned-release matrix is complete: all 210 optimization
invocations pass; there are no optimization timeouts, assertions or profile
errors. All 70 ODC-combination products pass separate whole-circuit DSEC.
Together with the six-arm matrix, the final ledger covers **630/630 products**:
620 default DSEC PASS plus 10 raw UNDECIDED entries discharged by exact
full-graph-pair binding to independent supplemental proofs. The raw statuses
are unchanged (`formal-product-ledger.json`).

| Clean release, integrated fast35 | Build % | Total SEQ % | Final AND sum | Time mean / median vs fresh TFO+CEX |
|---|---:|---:|---:|---|
| TFO+CEX control | 4.208656 | 4.765709 | 19,444 | 1 / 1 |
| TFO+CEX + polarity + auxiliary | 7.057889 | 7.696956 | 18,319 | 1.1371 / 1.0550 |
| Same new strict stage + existing ODC/H2 | 8.958466 | 9.597533 | 17,507 | 36.7280 / 3.7612 |

**The ODC combination is not a further improvement in the headline averaged
quality metric over the previous ODC release.** Against that earlier,
input-hash-matched TFO+ODC+CEX batch, pooled final ANDs improve from 17,661
to 17,507 (154 fewer; 15 better / 11 equal / 9 worse), but average Build falls
from 9.042818% to 8.958466% (minus 0.084352 percentage points). Average total
SEQ is almost unchanged: 9.599871% to 9.597533% (minus 0.002338 points).
Gains on larger circuits can improve pooled AND counts while losses on small
circuits lower the equal-circuit average. These are different metrics, not
conflicting results. The largest pooled gains include systemcdes +53, SPI +35,
i2c +23 and USB +21; des_area loses 18.

Observed integrated per-circuit time ratios against the earlier ODC batch are
0.8458 mean / 0.8788 median (two-command flow 0.8556 / 0.8984). These batches
were run at different times on a shared host, so the roughly 15% measured
reduction is not an isolated timing guarantee. The ODC package remains much
more expensive than the improved strict-only stage. Its B128/q320 material
budget, L16 iterations and weaker boundary obligations are unchanged.
The strongest conclusion of this round is the substantial improvement in
cheap native strict construction, not an across-the-board improvement after
ODC. Keep the new strict switches independently selectable with ODC too.

For the requested post-scorr view, using the control standalone `scorr_time_ms`
for all matched circuits, mean/median `T(stran2)/T(scorr)-1` are 8.2772 / 1.7647
(control), 10.3381 / 2.6364 (new strict), and 710.1028 / 11.5490 (new + ODC).
All 35 denominators are positive; no exclusions or clamping were used.
These large ratios are sensitive to tiny scorr denominators and outliers;
use the direct paired pipeline ratios above for the main engineering comparison.
See `post-scorr-overhead.json`, `odc-comparison.json`, and `release-analysis.json`.

### What was fixed, without adding a replacement pass

The native single-root iterator still constructs AND/inverter recipes from
its selected divisors. The existing complete root proof, composition, actual
insertion and exact cleanup gain checks still decide what may be committed.
No rewrite, SAT recipe synthesis, multi-output construction, extra retry pass,
retiming or state encoding was added. Q4/W8, B16/q20, j5/w8, F1/C1000/b100,
initial scorr, E5 switches and the normal epoch stopping rule stay fixed.

Two independent mechanisms are exposed separately:

1. **Complete polarity classification for empty labels.** In
   `Gia_ManFindOneUnateInt`, the previous `if (...) positive; else if (...)
   negative` records only the positive literal when both polarities satisfy
   an empty OFF set. This is a real native iterator representational omission,
   not merely a small q limit. The opt-in policy records both legal polarities.
   It is scoped to strict SEQ RootPass and reset before other stages/commands.
   Other resub clients and the COM/ODC constructors retain their old policy.
2. **Separate auxiliary observations for strict Build.** Preserve all 2,048
   Q4/W8 reset observations and append 256 independent combinational samples
   with free PIs and ROs. A single snapshot-shared evaluation creates the extra
   word per Q lane; no SAT call and no whole-graph simulation per root are added.
   The resulting 2,304-row table guides divisor ranking/core selection and the
   existing Build iterator. Direct matching keeps the original reset teacher,
   although its selected pool can change. The reachable CEX bank and its Q/W
   layout are unchanged. The extra random stream is independent and deterministic.
   The table is immutable while cursors run and freed at snapshot teardown.
   Root-local CEX overflow keeps the old path and explicitly profiles a skip.

**Free-RO observations are not reachable CEX.** They strengthen the sampled
construction problem and may exclude a recipe that is valid only on reachable
states. They confer no proof privilege. Using them is an explicit conservative
quality tradeoff, not a reachability claim or a complete strict search.

### Mechanism evidence: available information did not guarantee construction

For simple_spi's first strict snapshot, root 894 has exactly the same ordered
pool `[78,86]` in the compared runs. Its old target signature is all zero;
divisor 78 is also all zero, while divisor 86 has 126 ones. The useful recipe
is `n78 AND n86` (native recipe `[156,172]`, output `-2`). With the old policy,
both q20 and q320 generate **zero Build candidates** for this root; the trivial
zero/existing candidates do not prove. Either the polarity repair or the
auxiliary observations makes the native iterator produce the useful one-AND
recipe at stage 1, rank 1. Independent universal combinational root CEC and
full-circuit DSEC both pass; isolated exact cleanup removes 4 ANDs.
This is a concrete missed construction, not a general single-root upper bound.

The native self-test exhausts every nonempty subset of the four two-input
valuations, all 16 target truth tables, and all eight distinct one-AND/inverter
functions. There are **520 compatible recipe obligations**. The old iterator
misses **228**; the new polarity policy misses **0**. This is completeness for
that stated small language/test space only, not arbitrary recipe completeness.

First-snapshot traces on i2c, simple_spi, ss_pcm and usb_phy confirm identical
source graphs and bit-for-bit preservation of every original observation.
There are **238 newly selected Build recipes** absent from old generated
candidates; **200** use only materials already in the old pool. All 238 prove
in the native combinational stage. However, most ordered pools also change:
only 2 have the identical full ordered pool. Thus the overall gain includes
better material selection as well as better native construction; it cannot
all be attributed to fixing the iterator after a fixed pool.

The old active reachable teacher makes 2,741 bounded queries across fast35:
167 SAT, 2,574 UNSAT, zero UNKNOWN, with 0.323468 seconds total active-query
work. Thus this batch does not suggest CDCL timeout is the principal bottleneck.
Most queried opposite values cannot occur inside the configured reset horizon;
spending more conflicts on those same UNSAT predicates will not create samples.
This is bounded UNSAT, never an invariant or replacement certificate. Under the
new optimization trajectory, existing queries rise to 3,478 (174 SAT, 3,304
UNSAT), even though the auxiliary feature itself adds no queries. Fixed per-
snapshot budgets do not imply identical numbers of successful descent epochs.

A separate audit of 141 first-round ODC-selected recipes is especially useful:
**139 pass strict root equivalence**, with the root exposed as an additional
output and every original PO/RI retained. Fresh independent sequential checks
and the native strict proof lane agree; **all 139 pass the native combinational
proof stage**. Two are refuted under the strict root obligation. This shows
that much of this sampled ODC success was discoverable without weaker ODC
semantics. The ODC material/search budgets (B128/q320), spatial windows and
snapshots differ, so this is not a decomposition of all final ODC gain.

### Controlled alternatives and failures

The six-arm full fast35 prototype comparison used the same native strict
search budgets and both experiment flows. Percentages below are means of each
circuit's ordered Build or total SEQ gain divided by its normalized source ANDs.
Runtime ratios use per-circuit integrated pipeline times against that batch's
old control; final AND sums are supporting pooled counts.

| Strict TFO+CEX variant | Build % | Total SEQ % | Final AND sum | Extra AND removed | Better/equal/worse | Time mean / median |
|---|---:|---:|---:|---:|---|---|
| Previous release | 4.208656 | 4.765709 | 19,444 | 0 | 0/35/0 | 1 / 1 |
| Polarity repair only | 4.733426 | 5.308183 | 19,262 | 182 | 12/23/0 | 1.0522 / 0.9688 |
| Free-state auxiliary only | 6.996810 | 7.633133 | 18,331 | 1,113 | 21/7/7 | 1.1735 / 1.0976 |
| Both (review candidate) | 7.057889 | 7.696956 | 18,319 | 1,125 | 21/7/7 | 1.1552 / 1.0788 |
| Extra reachable tail observations | 4.825050 | 5.214369 | 19,315 | 129 | 21/10/4 | 1.1072 / 1.0914 |
| Equal-size independent reset observations | 4.196982 | 4.755617 | 19,432 | 12 | 3/28/4 | 1.0437 / 1.0075 |

The two mechanisms overlap strongly: polarity-only gains cannot be added to
the auxiliary-only gains. The combined incremental gain over auxiliary-only
is 12 ANDs. The equal-size random control does not support explaining the large
auxiliary gain solely by 12.5% more rows. Reachable tail samples help less.

On the initial eight-circuit pilot, pruning queries whose opposite value was
already impossible in the unroll had zero net gain; broadening query columns
added 13 ANDs. Completing one independently sampled SAT justification cube
added 15. Raising q20 to q320 at B16 added only 9. B128/q320 added 301, but
on des_area the pipeline rose from about 9.35 to 245.79 seconds. Q1/W32 at
the same 2,048 signature bits added 340, typically at 2–5x time. These are
bounded diagnostic samples, not all-fast35 results or impossibility claims.
The initial query prototype changed CO append order and hence SAT model
completion; its nonreproducing control is explicitly invalidated and excluded.

A ten-circuit follow-up tested two uniform restrictions: use free-state rows
only for constant targets, and use the one-transition image of an arbitrary
state. They recover some regressions but lose much of the useful gain on
SPI/i2c/USB. The latter is still not a reset-reachable sample. Neither is in
the review source; no circuit-name-specific policy was introduced.

### Why some cases regress, and why fewer candidates need not mean less time

All seven strict regressions are retained in the aggregate. On b03 and b04,
first-snapshot traces identify respectively 1 and 8 old selected recipes
excluded by auxiliary rows. Fresh independent checks of **all nine** expose
the target root as an additional output: each is sequentially equivalent from
reset but combinationally inequivalent with free ROs. This directly demonstrates
the conservative mechanism's lost sequential opportunities. It explains all
8 lost ANDs on b04; b03's final 4-AND loss also includes later trajectory changes,
so the first-snapshot witness alone is not its complete final decomposition.

In the clean integrated full batch, strict Build generated/submitted/proved/
selected counters change from **180,005 / 176,789 / 4,237 / 716** to
**25,296 / 21,458 / 7,167 / 1,133**. Roughly 86% fewer candidates are generated,
while more are proved and selected. This supports better candidate quality,
not just a larger search. It does not mean that every excluded old candidate
was meaningless, as the nine regression witnesses demonstrate.

The extra signature evaluation and copy cost totals only **0.004353 seconds**
across integrated fast35. But the existing divisor/core algorithms see a
larger and different relation and different optimization trajectories: profiled
SEQ divisor selection grows from 8.3403 to 13.0441 seconds; its nested TFO core
value work grows from 5.2202 to 8.3290. These nested clocks must not be summed.
This explains why the complete pipeline still costs about 14–16% more, despite
far fewer submitted candidates. The extra mechanism adds no SAT queries.

### Review source, operation and validation

The candidate depends on the previous commits 02f788aee (cursor cleanup),
f4fbe6631 (ODC signature feature), e571aba2b (validation report), and e29304187
(reachable strict CEX). Apply the incremental review change on that chain;
cherry-picking it alone onto production is not a complete integration.

The incremental source comprises `giaResub.c`, `cecTrans.c`, new
`cecTranStrictGuide.h`, `run_stran2_strict_guide.sh`, additive profile parsing and
parser/preset tests. All query/cube/ODC-reclassification/trace prototype hooks
are removed; `cecTranStrictCexActive.h` is unchanged from e29304187.

Use the opt-in preset with the compiled review binary:

```sh
ABC=/mnt/home/zhaoxiran/script2/evidence/strict_cex_refine/20260912/bin/abc-release \
  bash scripts/run_stran2_strict_guide.sh
```

`STRICT_GUIDE=0` disables the free-state table; `STRICT_BOTH_POLARITIES=0`
disables the polarity repair independently. Both default to 1 only in this
new preset. The ordinary command defaults remain 0. `ODC_ENABLED=1` enables
the existing ODC/H2 preset after strict processing. New additive fields
`strict_guide_{records,snapshots,source_rows,auxiliary_rows,skipped_overflow,prep_sec}`
aggregate per-snapshot increments. Existing strict CEX counters remain cumulative
and are parsed from the last epoch; absent fields remain N/A.

The release native self-test passes, including the exhaustive polarity check,
old-row preservation, free-state truth evaluation and explicit exclusion of a
sequentially valid recipe. All 24 Python profile/signature/preset tests pass
with the built binary, with no skipped command tests. The ASAN build instruments
both changed translation units (other ABC objects remain uninstrumented);
native self-tests and b04/i2c/SPI/ss_pcm pass, all four products also passing
independent DSEC. ASAN leak detection is disabled; this is not a whole-program
leak-freedom claim. Assertions remain enabled in every binary.

The six-arm matrix has 420 complete products: 412 default DSEC PASS, with 8
b13_opt UNDECIDED preserved in the raw CSVs. Those eight correspond to two
identical full graph-pair groups, both independently proven by the frozen
checker with `dsec -r -m -T 1800`. The cleaned control/release validation has
140 products: 138 default PASS; its two control b13_opt pairs match the already
proven pairs exactly. All 70 newly guided release products default DSEC PASS.
Graph identity checks preserve topology, full PI/RO/PO/RI interfaces and reset
values while ignoring names/comments. Exact file hashes are also retained.

Build provenance: assertions-enabled `gcc -g -O`; two changed translation units
compiled and linked with 1,375 unchanged objects from the frozen e29304187 tree.
Release binary SHA256:
`2a05311de06bffd231e83cfb12ccbacc86905cf7b12b715df035d8860a0e99aa`.
The final manifests include both changed C files, all included local feature
headers, preset/parser hashes and the independent checker identity.
A separate full build from this tree (`make -j16 ABC_USE_NO_READLINE=1`) also
passes the native suite and all 12 focused control/candidate products. Their
complete graph identities match the measured release, and all pass independent
DSEC. Full-build binary `bin/abc-full` SHA256:
`dafc89136a92491ab727fd6aad6f37e161f1145b25bb990df19f18501754d99d`.
See `identity-full.json` and `full-pilot.json`; the full matrix timings use
`abc-release`, not this separately built binary.


Evidence root: `/mnt/home/zhaoxiran/script2/evidence/strict_cex_refine/20260912`.
Key evidence: `analysis-6.json`, `release-analysis.json`, `candidate-counts.json`,
`attribution_analysis.json`, `witnesses.json`, `odc_classify.json`,
`regression-proof.json`, `supplement.json`, `release-graph-bindings.json`,
`identity-release.json`, and the frozen `source-*` / `bin` variants.
Raw full CSVs only are stored in
`/mnt/home/zhaoxiran/script2/experiment_reports/20260912_strict_refine_{old,free,both,both_free,tail,random}`
and `20260912_strict_guide_{control,release,odc}`; pilots and logs are in evidence.
Every experiment uses the same 35 input hashes, 1800-second invocation limit,
both flows and independent DSEC; resource snapshots are in launch records.

These experiments use one fixed independent auxiliary stream and the fast35
corpus. They do not establish seed-independent improvement or generalization
to the larger quick268/full corpus.

The strict gap is materially smaller, but not closed. The next unresolved
algorithmic question is how to use discriminating unreachable observations
without excluding valuable reachable-only recipes or adding a second search
pass. The tested constant-only and one-transition restrictions do not solve
that tradeoff. ODC also retains distinct boundary semantics, material budgets
and later snapshots; no evidence here establishes the theoretical limit of
native strict construction. The review recommendation is to expose both
switches, keep the conservative policy explicit, and avoid silently making
it the production default.

Budget accounting: this round retains the agreed 10 weekly-percentage-point
ceiling. The shared account reset during the run; exact task consumption
cannot be inferred. A conservative 7-point post-reset ceiling reserves at
least 3 points for the pre-reset interval; no extra budget was assumed.
The reset and checkpoint evidence is archived separately from quality data.

## Merge candidate: reachable signature teaching before strict SEQ Build (2026-09-12)

The user asked to extend CEX teaching to the non-ODC phase and compare TFO,
TFO+CEX, and TFO+ODC+CEX. The owned review tree is
`/mnt/home/zhaoxiran/abc-strict-cex`, branch `codex/stran2-strict-cex`, based
on `e571aba2be56ecef567127dd28b0bf35cb92b421` from the signature-guide branch.
It inherits that branch's cursor repair and H0–H3 ODC feature. Production
`codex/stran2` remains at `3836f6091079664641bf42764b8a03c2310f6b54`;
its unrelated edits and the uncommitted signature-tree preset were preserved.
This is an optional integration candidate, not a production default change.

**Result:** in strict TFO processing, the new mechanism removes 589 additional
ANDs on fast35 (5 better, 30 equal, 0 worse), with mean per-circuit runtime
ratio 1.1063 and median 1.0361. After the existing ODC/H2 portfolio, its net
increment over that previous version is only 48 ANDs (2 better, 31 equal,
2 worse), with runtime ratio 0.9901 / 0.9974. The latter timing difference is
too small to establish a speedup on this shared host.

### What changed, and what SAT constructs

The native single-root constructor still chooses divisors, generates a small
AND/inverter recipe, and submits that recipe to the existing strict proof,
composition, insertion and exact cleanup gain checks. SAT constructs only
**PI input traces that expose missing values**, never replacement recipes.
There is no new rewrite, cut replacement, multi-output constructor, retiming,
state encoding, or register optimization pass.

At an existing strict SEQ snapshot, after the ordinary Q/W simulation and
before any root iterator is started:

1. Scan roots in the existing structural MFFC order. A target qualifies when
   MFFC >= 2 and its entire current signature is constant. Select at most 64.
2. Build one shared reset unrolling over the configured W frames. For each
   selected root, ask whether the opposite value occurs in any of those
   frames. The recommended backend is the existing CDCL solver with Tseitin
   gate equations and 100 conflicts per query. A 500,000 object-frame bound
   prevents an unbounded unroll. The source graph's Value fields are untouched.
3. Complete a satisfying PI assignment and independently replay it on the
   original sequential graph from zero reset. Keep it only when that replay
   exhibits the requested value. UNSAT and UNKNOWN supply neither a sample
   nor a replacement certificate. All old PIs and synchronous RI equations
   are represented; ROs are never free initial-state variables in this mode.
4. Deduplicate into a bank of at most 64 PI prefixes for the command. These
   replace random lanes inside Q; retain initial scorr CEX too. If the combined
   corpus overflows Q, use the existing wider-source/root-lane-selection path.
   Replay once per snapshot, shared across roots. There is no whole-graph
   simulation per root and no mutation of an active iterator's signatures.
5. Later ordinary epochs reuse these PI prefixes on their current reset graph.
   No old node ID, RO value, care mask or proof certificate crosses a snapshot.
   No extra epoch is added when the normal AND-descent loop stops.

Q4/W8, strict B16/q20/j5/w8, F1/C1000, native construction families and all
proof/commit policies stay fixed in the comparison. Actual epoch counts may
increase when extra profitable replacements keep the existing loop running.
COM receives no new active sampler. The strict bank is freed before ODC;
ODC continues to use the previous long-observation/H2 package. H2's auxiliary
free-PI/RO observations are **not** reachable sequential CEX; its earlier
correctness/tradeoff description below still applies.

This follows the expressive-pattern direction of
[Simulation-Guided Boolean Resubstitution](https://arxiv.org/abs/2007.02579)
and [A Simulation-Guided Paradigm for Logic Synthesis and Verification](https://si2.epfl.ch/demichel/publications/archive/2022/sonia.pdf).
Those works motivate informative simulation patterns; the local adaptation
here is reset-reachable bounded PI witnesses feeding the existing sequential
constructor and its fixed candidate budget. No novelty claim is made for
simulation guidance or SAT-generated distinguishing inputs.

### Experiments that distinguish the mechanism

The first prototype only harvested packed BMC counterexamples from later
strict candidate proofs and consumed them at an existing next epoch. In an
8-circuit, four-arm pilot (off / initial-only / collect-only / replay), only
i2c acquired useful prefixes; every arm had the same final AND count.
Induction counterexamples were excluded because their reset reachability was
unproved. This passive interface's limited coverage did not refute CEX teaching.

Active missing-value queries with the circuit-based solver then reduced i2c
1509 -> 1199 and usb_phy 636 -> 614. Collecting samples without consuming
them reproduced the control; equal-length independent random PI prefixes did
not reproduce the improvements. Selecting CDCL upfront, with the same 64-query
and 100-conflict limits, improved i2c further to 1136. It was not a fallback
after an UNKNOWN. All focused products passed independent DSEC. Random controls
use their own subsequent trajectories, so their later query counts/prefix
lengths are not asserted identical after the graphs diverge.

On full fast35, 24 circuits triggered queries; 9 acquired witnesses and
5 improved. There were 2,741 queries, 167 SAT, 2,574 UNSAT and 0 UNKNOWN,
retaining 122 prefixes across circuits. Unrolling, solving and validation
together cost 0.331508 seconds across the 35 integrated strict runs.
Strict SEQ generated candidates fell from 211,015 to 201,498, and submissions
from 207,406 to 197,847. These fields describe the strict stage, not all ODC
enumeration. Initial scorr retained zero CEX on every circuit in this corpus.
The two common flows produced identical quality and final graphs.

The strongest attribution comes from first-epoch snapshots with identical
graphs and exported complete simulation tables:

* i2c root 1045 has the same 16 divisors in exactly the same order in both
  runs. Its target remains all-zero in both tables, but 11 distractor divisor
  columns change. All 20 old Build candidates are refuted by the new reachable
  samples. Native construction now generates `root = n155 OR n1039`, encoded
  as one inverted AND. It is rank 7 in the constructor and fits q20. A separate
  insertion into the original snapshot, with complete PO/RI cleanup and a
  fresh DSEC proof, reduces 1630 -> 1625 ANDs: exact isolated gain 5.
* Raising the old first-snapshot budget to q80 still misses that recipe.
  At q320, the old constructor generates, proves and selects it at recorded
  rank 92. This is a budget/order loss, not theoretical inexpressibility.
* i2c root 1075 has the same ordered 8-divisor pool. The old q80 and q320
  runs both emit the same 35 Build candidates and miss a two-AND recipe that
  the new q20 run generates at rank 8. Eighteen of its old q20 Build candidates
  fail the new samples. Independent isolated insertion/DSEC confirms gain 3.
  This implicates the finite heuristic construction path as well as ordering;
  it is not a completeness result about all possible native or SAT search.
* usb_phy root 736's useful one-AND recipe uses divisors already present in
  the old pool; new sampling changes target ones from 0 to 1 out of 2048.
  All 20 old Build candidates fail the new samples. Fresh isolated DSEC and
  cleanup confirm gain 4. Here the overall pool/ranking also changes.

Across i2c's first epoch, 96 newly selected Build recipes were absent from
the old generated set; 74 use only old-pool materials, but only 2 have an
identical complete ordered pool. Therefore the total improvement includes
better divisor selection/ranking, not solely an internal constructor effect.
All 96 selected recipes match both old and new reachable observation tables;
the improvement is which useful recipe gets generated and proved.

### Complete fast35 comparison

All four arms run both common flows (280 products), same input hashes,
1800 seconds per invocation, and 48 maximum experiment workers. Every
optimization invocation passed execution/profile checks, with no timeout or
assertion. Reduction below is the equal-circuit mean of gain/source ANDs;
Build is `seq_build_ordered_and_gain`, total SEQ is `seq_stage_and_gain`.
These exclude initial scorr and COM reductions. All arms have 1,776 latches.
Runtime includes initial scorr and optimization, excludes normalization and
independent equivalence checks, and is the mean / median of per-circuit time
ratios against TFO-only. It is not a ratio of summed times.

| Integrated configuration | Ordered Build/source | Total SEQ/source | Final AND sum | Runtime mean / median ratio |
| --- | ---: | ---: | ---: | ---: |
| TFO only | 3.441234% | 3.984869% | 20,033 | 1.0000 / 1.0000 |
| TFO + reachable CEX | 4.208656% | 4.765709% | 19,444 | 1.1063 / 1.0361 |
| TFO + ODC + CEX / H2 | 9.042818% | 9.599871% | 17,661 | 47.0685 / 5.9606 |
| Previous ODC + H2 reference | 9.013059% | 9.556694% | 17,709 | 47.2279 / 6.7607 |

The ODC arm explicitly adds the existing quality-oriented B128/q320,
D4/L16 ODC portfolio after the fixed strict B16/q20 stage. Its roughly 47x
mean / 6x median time ratio is the cost of that added portfolio, not the cost
of the new strict CEX sampler. This is a configuration comparison, not equal
total-work-budget TFO versus ODC. The previous ODC reference already incurred
47.2279x mean time. Pipeline sums (supporting totals only) are 25.880 s,
26.775 s, 2243.991 s and 2252.768 s in table order.

Strict gains by circuit: ethernet +6, i2c +373, simple_spi +116,
ss_pcm +72, usb_phy +22 ANDs. After ODC, the incremental differences relative
to the previous ODC/H2 implementation are i2c +47, simple_spi +4,
ss_pcm -2, usb_phy -1. Thus the 589 strict gain and the 48 post-ODC gain
must not be added: many opportunities overlap with those ODC already recovers.

The two small post-ODC regressions both stop with no profitable proved
candidate at round 6 / 8; neither reaches L16 or fails a formal proof budget.
The stronger strict prefix changes the subsequent finite ODC search graph.
This local regression attribution is partial: a specific missing final ODC
recipe has not been isolated, and there is no per-circuit repair or route rule.

### Correctness and integration checks

Native tests include exhaustive enumeration of all 16 two-frame PI traces in
a small sequential example: one target can change, while another depends on
a permanently-zero register and cannot. Both SAT backends agree with replay.
The bank tests cover reset rejection, no-split rejection, duplicate handling,
induction exclusion, horizon bounds and PI-only transfer across register-count
changes. New clause construction is outside assertions. Assertions remained
enabled throughout.

Independent DSEC initially passed 276/280 products. Four b13_opt products
(both TFO arms, both flows) returned **UNDECIDED**, encoded `FAIL(0)` by the
existing runner. Their source/final graph pairs are identical. A separate
frozen reference checker proved that exact pair with
`dsec -r -m -T 1800` (checker-internal retiming disabled), reporting 0.01 s.
Hash/graph identity binds that supplementary proof to all four products.
The raw CSV statuses were preserved. Final independent proof coverage is
280/280; there is no claimed PASS from exit status or simulation alone.

The previous ODC reference reproduces all 70 frozen H2 final graphs from the
earlier release. AddressSanitizer on the changed cecTrans translation unit
passed native tests and four changed focused strict/ODC products; unchanged
dependencies came from the full build. Eight instrumented focused products
also passed independent DSEC, and the three isolated native-recipe witnesses
have separate DSEC proofs. The shared profile parser and signature tests pass
(11 + 5), as do four new cumulative-counter/preset tests. Strict counters take
the last cumulative epoch record rather than summing repeated bank counts.

The first build attempt lacked readline headers; continuing with
`make -j16 ABC_USE_NO_READLINE=1` completed the full tree. Only mainUtils.c
uses that macro; there was no struct/ABI change. Later builds recompiled the
changed translation unit with assertions. Tested binary is `bin/abc-v3` under
the evidence root, with source and binary hashes in `identity_v3.json`.
The sampler's production code is identical to that binary's frozen sources.
The new wrapper's default was subsequently set to the faster TFO+CEX route;
all matrix arms had explicit ODC/CEX settings, so their commands are unchanged.

### Reproduction and evidence

The bare commands retain their previous behavior. The new wrapper defaults
to TFO+CEX, CDCL, with the same Q4/W8/q20/j5/w8 settings:

```sh
ABC=/mnt/home/zhaoxiran/abc-strict-cex/abc \
AIG_DIR=/path/to/inputs TMPDIR=/path/to/owned/scratch \
TIMEOUT=1800 MAX_PARALLEL=2 JOBS_PER_EXPERIMENT=6 \
SKIP_DSEC=0 KEEP_ARTIFACTS=1 \
ODC_ENABLED=0 CEX_ENABLED=1 \
bash /mnt/home/zhaoxiran/abc-strict-cex/scripts/run_stran2_strict_cex.sh
```

Use a fresh result directory for every invocation. Choose `(ODC_ENABLED,
CEX_ENABLED)` as `(0,0)`, `(0,1)` or `(1,1)` for the requested three arms.
The fourth reference uses `(1,1)` with `STRICT_CEX_MODE=0`. CEX_ENABLED=0
disables constructor teaching, never the proof oracle's internal CEX logic.
The wrapper validates its settings and overrides inherited teacher variables.
Diagnostic strict modes are 0 off, 1 passive collect, 2 passive replay,
3 passive random control, 4 active replay, 5 active collect, 6 active random
control. `STRICT_CEX_SOLVER=0/1` selects CBS/CDCL upfront. The wrapper maps
these to `ABC_STRICT_CEX_MODE`, `ABC_STRICT_CEX_SOLVER`, and the independent
`ABC_STRICT_CEX_INITIAL` control. ODC retains its existing H2 options.

Evidence root: `/mnt/home/zhaoxiran/script2/evidence/strict_cex/20260912/`.
Key files: `plan.json`, `identity_v1/v2/v3.json`, `v1/v2/v3.json`,
`pilot_odc.json`, `check_focus.json`, `trace_analysis.json`,
`trace_refutations.json`, `budget_trace_analysis.json`, `witnesses.json`,
`matrix.json`, `analysis.json`, and `audit_b13/result.json`. The private trace
source/binaries are preserved as diagnostic artifacts, not merged hooks.
Complete raw CSVs only are in
`script2/experiment_reports/20260912_strict_cex_{tfo,tfo_cex,tfo_odc_cex,odc_reference}/`;
each directory contains `stran_current_stran.csv` and `stran_current_stran2.csv`.

### Remaining limits and stopping point

This is a measured improvement to strict single-root Build under a small
sample-acquisition budget. It does not establish completeness or universal
quality monotonicity. Only constant observed roots are queried; other aliases,
values first reachable beyond W, the 64-root priority/cap, bank saturation,
and heuristic core/recipe restrictions remain. Four circuits receive new
witnesses without a quality gain. Random-lane replacement does not preserve
every old random sample, even though retained initial CEX remain represented.
The strict bank is not yet fed into ODC, and this is not general sequential
ODC learning. A development fast35 corpus and one shared-host timing run do
not establish unseen-corpus generalization or a statistically reliable small
speed difference. No unproved or simulator-only result was committed.

The requested non-ODC extension, mechanism attribution and full configuration
comparison are complete. Stop at the reviewed opt-in candidate rather than
launching another algorithm direction in this task. This round used the
research-auto default ceiling of 10 weekly percentage points; the shared
account moved from 77% to 81% at the completion checkpoint. This is shared,
rounded account usage, not a precise task consumption measurement.

## Merge candidate: targeted signature guidance (2026-09-12)

The user requested a merge-ready improvement to the existing single-root
constructor. Source commit: `f4fbe6631`; separate cursor cleanup: `02f788aee`. The review branch is `codex/stran2-signature-guide`, based on
`3836f6091079664641bf42764b8a03c2310f6b54`. Production `codex/stran2` and its
unrelated working-tree edits were preserved. This entry documents an optional
candidate; the approved baseline below remains the production default.

The implementation strengthens the observation table supplied to native
core/Build construction. The constructor still builds a recipe for one root,
and the existing boundary proof, composition check, insertion and exact gain
check decide whether it can replace that root. It adds no rewrite pass,
multi-output synthesis, new divisor family, or SAT-generated recipe.

### Algorithm and correctness contract

1. At each immutable ODC discovery snapshot, evaluate one deterministic word
   (64 assignments) with free combinational inputs: PIs and register outputs.
   This costs one graph traversal shared by all roots and uses a separate RNG.
2. If a root has only one target value under the original observation care,
   append its and the complete divisor pool's auxiliary columns. In H2, if
   this word is also constant, ask bounded SAT for the opposite root value
   missing from that auxiliary word.
   SAT assigns input values only. There are at most 64 queries per snapshot,
   each capped at 100 conflicts. A satisfying partial assignment is completed
   into 64 concrete lanes; only the root/pool union cone is evaluated.
3. Preserve every original care observation. Compact the joined rows only
   when the full divisor vector **and target label** are equal. Opposite
   labels for the same pool assignment remain a conflict and stop this
   impossible construction attempt. Feed the resulting table to the existing
   constructor with its original pool, ranks, q and construction families.
4. Every candidate still requires the existing formal boundary obligations
   and composition/commit checks. Auxiliary samples confer no proof status.
   SAT UNSAT/UNKNOWN here neither proves a replacement nor adds a sample.

Free register-output assignments are **not reachable sequential CEX**. They
strengthen the construction constraints and can exclude legal sequential/ODC
recipes. H3 also triggers when a sampled root/divisor equality or complement
is disproved by the auxiliary word; it is an experimental quality tradeoff.
None of these modes guarantees per-circuit monotonic improvement. This does
not complete the research on reachable, observability-aware CEX teaching.
It also does not establish completeness of the native constructor relative
to exact SAT synthesis: missing divisors, restricted recipe families and
budget/selection gaps remain separate possible causes of lost opportunities.

The integration replaces the prototype's global scratch context and fixed
joined-buffer size with per-snapshot ownership and dynamic capacity. A private
SAT AIG with an explicit literal map leaves source `Value` fields untouched;
CI ordering, buffers and native XORs are handled explicitly. Cone evaluation
uses an iterative stack. The profile includes early-return checks, preparation,
SAT outcomes and compression counts; SAT seconds are nested within guide
seconds and must not be added twice.

An independent memory check also exposed an existing ODC cursor leak with H0:
only caches were freed, leaving the frozen pool and ranks allocated each round.
The branch uses the existing complete cursor destructor at the same cleanup
point. This is a separate resource-lifetime repair, with no algorithm change.

### Reproduction

Build with assertions enabled, e.g. `make -j16 ABC_USE_NO_READLINE=1` on this host.
From a fresh result directory, run:

```sh
ABC=/mnt/home/zhaoxiran/abc-signature-guide/abc \
AIG_DIR=/path/to/inputs TMPDIR=/path/to/existing/scratch \
TIMEOUT=1800 MAX_PARALLEL=2 JOBS_PER_EXPERIMENT=8 \
SKIP_DSEC=0 KEEP_ARTIFACTS=1 \
bash /mnt/home/zhaoxiran/abc-signature-guide/scripts/run_stran2_signature.sh
```

`SIGNATURE_GUIDE_MODE=0/1/2/3` selects the arm; the new preset defaults to H2.
The bare command defaults to H0 and `run_stran2_quality.sh` is unchanged.
Direct `-H` usage requires care-aware `-k -J` construction, spatial windows,
`ABC_CEX_MODE=2` and `ABC_CEX_COMPRESS=4`; incompatible combinations are rejected.
The preset holds the approved baseline's Q4/W8, long Q1/W256 observations,
B128/q320 ODC budget, D4 windows and L16 cap fixed. It runs both common flows.

### Fresh final-binary fast35 results

All 35 original input hashes are paired, with both `scorr-stran` and integrated
`stran2`, all four modes, 1800 seconds per invocation and 64 maximum workers
per matrix. All 280 final-binary rows are execution/parser/DSEC PASS; there
are no timeouts, assertions, profile errors or excluded cases. Latch sum is
1,776 in each arm. Quality agrees across the two flows and every final graph
(excluding names/comments) matches the corresponding frozen research prototype.

The following is **integrated `stran2`**. Reduction is the arithmetic mean of
per-circuit gain divided by normalized source ANDs; Build means
`seq_build_ordered_and_gain`, total SEQ means `seq_stage_and_gain`. Runtime is
the arithmetic mean / median of per-circuit pipeline-time ratios against H0,
including initial scorr and excluding normalization and independent DSEC.

| Mode | Ordered Build/source | Total SEQ/source | Final AND sum | Better/equal/worse vs H0 | Runtime mean / median ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| H0: Control | 6.711162% | 7.254798% | 18,697 | 0/35/0 | 1.0000 / 1.0000 |
| H1: One auxiliary word | 8.868207% | 9.411842% | 17,806 | 14/21/0 | 0.9176 / 0.9767 |
| H2: Recommended: word + missing-value SAT | 9.013059% | 9.556694% | 17,709 | 14/21/0 | 0.9218 / 0.9851 |
| H3: Also break observed aliases | 9.072764% | 9.616399% | 17,689 | 14/18/3 | 0.8488 / 0.9821 |

Recommended H2 removes 988 additional ANDs in aggregate,
with 14 circuits better, 21 equal and 0 worse.
Its mean runtime change is -7.82%, with median
-1.49%. These are fixed-seed observations on a
selected fast35 corpus, not a generalization or statistical speed guarantee.
Some individual runtimes increase; sub-second cases are sensitive to launch
and scheduling variation. The complete per-case data are retained.
H3 has three known one-AND regressions (b09, b09_opt, b11_opt), which is why
it is not the recommended preset despite its better aggregate reduction.

The H2 ODC phase generates 899,020 candidates versus
1,904,077 for H0, proves
14,823 versus
9,487, and selects
966 versus 658.
ODC proof time totals 528.725s versus
776.047s. H2 guide preparation totals
0.001330s, guide work 0.135382s,
including SAT solving 0.002945s. The interpretation is that
more informative signatures avoid many unproductive recipes and expose more
useful native constructions. At the fixed q/W budget, targeted assignments
supply distinctions missing from the original observation table. Legacy `seq_constructed_*` counters omit this ODC phase
and must not be used as its candidate totals.

### Validation and evidence

- Clean full build and the final cursor-fix rebuild; assertions enabled.
  Native `&stran_resub_test`, 21 combined signature/closure/report Python tests,
  and the 11 profile tests pass. New native tests cover a 513-word input table,
  exact truth-row preservation, contradictory labels, bounded rare-value SAT,
  UNSAT/UNKNOWN, CI mapping and untouched source scratch fields.
- Final binary focused USB H0/H1/H2/H3 and i2c H2: 5/5 independent DSEC PASS.
  Final AddressSanitizer selftest and USB H0/H2 plus i2c H2 runs pass, with
  leak detection enabled and independent DSEC for all three final products.
  Instrumentation covers the changed C translation units; unchanged dependencies
  come from the clean build. Pre-fix leak reports are retained.
- Five additional quick-corpus circuits selected by header structure and
  SHA1(relative path), without constraints/justice/fairness, are tested in
  H0/H2 and both flows: 20/20 execution and independent DSEC PASS. All bad-state
  predicates are retained as observed POs. Existing ABC initialization
  normalization adds PI/mux/phase state for uninitialized registers, which is
  audited explicitly. H2 improves three integrated results and ties two;
  this small sample is regression coverage, not a broad corpus claim.
- The first hardened full matrix, before the cursor lifetime repair, also has
  280/280 PASS rows. The final matrix is the release result above; the earlier
  matrix is retained as separate provenance, not mixed into timing averages.

Final binary SHA256: `b065ca44164f42f5460fdd2bc1943138b6c5faa4ffe2f97d4c822ee9e1b64def`.
Complete release raw CSV pairs are under
[`20260912_signature_guide_release_h2/`](/mnt/home/zhaoxiran/script2/experiment_reports/20260912_signature_guide_release_h2)
and corresponding `h0`, `h1`, `h3` directories. Build/source hashes, command
settings, all logs, graphs, independent audits, prototype comparison, profile
analysis and the scoped patch are archived in
[`signature_guide_merge/20260912/`](/mnt/home/zhaoxiran/script2/evidence/signature_guide_merge/20260912).

## Approved development baseline: TFO + complete-information ODC (2026-09-10)

The user selected the **6.7111623876%** fast35 Ordered Seq Build/source
configuration as the next production development baseline and asked to pause
further algorithm exploration for technical discussion. This entry supersedes
the historical sections below when they describe an older "current" baseline.

The selected source is `bed995558b0a44d4dc6455a2056bce8ea658c447`, merged into
`codex/stran2` while retaining its `9be377928` frontier reference-scratch repair.
TFO is already part of this selected source. The integration includes its ODC
window/boundary proof and batch-commit dependencies, complete reachable
observation quotient before native core/Build search, and exact bidirectional
bit transposition. It stops before the subsequent core-reuse, witness,
minimum-support SAT, and local-realization-value experimental commits.

The reproducible baseline entry is
[`scripts/run_stran2_quality.sh`](/mnt/home/zhaoxiran/abc/scripts/run_stran2_quality.sh).
Run it from a fresh result directory, setting `ABC`, `AIG_DIR`, and an existing
`TMPDIR` as needed. It calls the common paired runner with fixed algorithm
settings; `TIMEOUT`, `LIMIT`, worker counts, `SKIP_DSEC`, and `KEEP_ARTIFACTS`
remain runner controls. The generic runner and bare ABC command defaults are
not the baseline preset.

- Strict prefix: B16/q20, Q4/W8, Kit/BDC, F1/C1000, TFO enabled.
- Additional ODC: B128/q320/L16, spatial D4, existing alternate care cores,
  full divisor pool, CBS plus sequential boundary proof, no extra ODC Direct.
- `ABC_CEX_MODE=2 ABC_CEX_COMPRESS=4 ABC_CEX_PACK_FAST=2`, projection toggle 0.
  Long Q1/W256 observations are simulated once per immutable snapshot; rows
  are merged only on equal target and complete pool values under care.
- "Complete information" means the complete supplied observation matrix,
  not exhaustive reachable-state coverage. Observations guide construction;
  formal candidate/bundle proof requirements remain in force.

Frozen reference and fresh merged full fast35 result: both flows 35/35 execution/parser PASS,
Build/source mean 6.7111623876%, total SEQ/source mean 7.2547975419%, final
AND sum 18,697, latches 1,776. This is a fixed-seed selected fast corpus,
not a full58/quick268 or statistical generalization result.

Merge validation is complete; the result and exact source/binary
identities are recorded under
[`integration/`](/mnt/home/zhaoxiran/script2/evidence/cex_reconstruction/20260910/integration).
The source builds with assertions enabled; `&stran_resub_test` and all 11
committed-parser tests pass. All 70 final graphs (excluding symbols/comments),
per-case quality fields, and per-round ODC counts match the frozen reference.
The committed parser also reproduces the quality/accounting fields of all
70 logs independently of unrelated working-tree parser additions. There were
no execution, timeout, assertion, or profile failures in the full matrix.
Eight selective final-network DSEC checks pass: b03/b04 focused and b05/des_area
full results, each in both flows, after consistent positional port naming.
The full matrix explicitly skips DSEC; these are selective formal audits.
Complete raw CSVs are in
[`20260910_cex_quality_mainline/`](/mnt/home/zhaoxiran/script2/experiment_reports/20260910_cex_quality_mainline).
Existing unrelated working-tree edits are preserved.
Build command on this host: `make -j16 ABC_READLINE_LIBRARIES=-l:libreadline.so.8`
(the installed readline library has a versioned filename).

Updated 2026-09-05. One development tree: `/mnt/home/zhaoxiran/abc`,
branch `codex/stran2`. Goal: preserve high-quality total SEQ and ordered
Seq Build reduction while reducing runtime. First unresolved task: the
fib_05 proof-context/UNKNOWN quality regression. No proof-policy fix yet.

## Tested Configuration

Algorithm: E5 + immutable-page reuse + Stage-3/Stage-5 review repairs +
closure-complete profiling. Cleanup changes tools/docs only, not `src/`.
Tested source: `45a89cbdb9644b62c923bf5d58890c15dc05f5c6`;
later documentation base: `aa163f7e132533539eba6b867d93fbf78717bfa6`.
Tested binary SHA256:
`e7e3a9c6bedc623a6cd3fe0cbfd10728a1ac401b75f98fd767f069a39ae7d7b5`.

Both flows use `-Q 4 -W 8 -q 10 -j 5 -w 8 -C 1000 -b 100 -V 0 -E 5 -p`.
Compare default `&scorr; &stran` with integrated `&stran2`, which runs its
own default scorr and retains reachable CEX as teaching trace lanes.

Raw evidence: `/mnt/home/zhaoxiran/script2/experiment_reports/20260905_stran2_review_fixes/`.
Current pair: `stran_fixed_stran_E5_Q4_W8_q10.csv` and
`stran_fixed_stran2_E5_Q4_W8_q10.csv`; before-fix pair also retained.
All four groups: 268 matching input hashes, 1,072 execution PASS rows,
zero timeouts/assertions/ABC/profile errors or missing/malformed rows.
DSEC SKIP=1,072, not a full equivalence audit. Separate fixed-output DSEC
audits passed on cal103 and fib_05. Additional diagnosis retained three
distinct DSEC pairs and one PDR property, all passed.
This is a historically all-PASS selected corpus, not the full 330-case set;
one observation per configuration, with shared-host noise. Timeout was
1800 s per invocation, not a common end-to-end deadline.

## Runtime: Equal Weight Per Circuit

The user's requested approximation is
`R2 = mean_i(T(stran2)_i / T(scorr)_i - 1)`.
Use the paired standalone scorr measurement, not the integrated CSV's zero
placeholder. For standalone stran, `R1 = mean_i(T(stran)_i / T(scorr)_i)`.
These are means of individual ratios, NOT ratios of summed times.

| 268 paired circuits | Standalone stran | Stran2, initial scorr approximately removed |
|---|---:|---:|
| Arithmetic mean wall-time multiple of scorr | 17.5406x | 15.5316x |
| Median wall-time multiple | 10.0671x | 8.2091x |
| Arithmetic mean user-time multiple | 18.9485x | 16.9212x |
| Mean extra wall seconds per circuit | 26.0105 | 22.2314 |

Stran2's mean relative wall overhead is 2.0090 scorr units lower. This is
not a claim that every case speeds up by that amount. Four wall estimates
are slightly/meaningfully negative because separate short runs differ;
retain them without clipping under the requested approximation. Do not
interpret them as negative physical work or compute a geometric mean of
these net estimates. The median provides a less tail-sensitive companion.

## Reduction And Quality

| Metric | Default scorr | Scorr + stran | Stran2 |
|---|---:|---:|---:|
| Final ANDs, 268 circuits | 4,585,633 | 4,535,306 | 4,522,829 |
| Extra ANDs removed after scorr | 0 | 50,327 | 62,804 |
| Extra reduction / scorr ANDs | 0 | 1.09749% | 1.36958% |
| Final latches | 363,418 | 363,418 | 363,418 |
| Total SEQ AND gain, 261 profiled circuits | n/a | 20,774 | 23,406 |
| Ordered Seq Build AND gain, same 261 | n/a | 11,105 | 13,192 |
| Total SEQ gain / input ANDs, same 261 | n/a | 0.324040% | 0.365094% |
| Ordered Seq Build gain / input ANDs, same 261 | n/a | 0.173219% | 0.205773% |

All-input totals: 6,485,261 ANDs and 530,790 latches. Profiled input ANDs:
6,410,945. Seven inputs reduce to zero AND/latches at scorr and have no
root profile; no missing profile fields were imputed. Their paired scorr
and final counts are explicitly measured as zero.

Stran2's 62,804 extra AND reduction consists of COMB 39,398 + SEQ 23,406.
Ordered Seq Build contributes 13,192, 56.36% of SEQ and 21.01% of all extra
reduction; it is a subset, not a quantity to add to total SEQ again.
Compared with scorr: 199 better / 69 equal / 0 worse final AND results.
Compared with stran: 90 better / 142 equal / 36 worse; 12,477 extra ANDs
removed overall. Total SEQ gain +12.67%; ordered Seq Build gain +18.79%.
No additional latch reduction beyond scorr in this matrix.

SEQ proof-origin Build generated/proved/selected:
stran 11,742,415 / 31,085 / 3,712; stran2 8,322,395 / 33,208 / 4,129.
Actual SEQ-commit Build selections are 3,723 / 4,142 respectively;
proof origin and commit phase are different attribution dimensions.

## What Was Kept

- E5 = exact TFI CI-count reuse/lazy ties plus an exact contradiction check
  on the selected divisor pool. Equal divisor observations with opposite
  target bits mean no function of that pool can fit the observations, so
  Build can skip the impossible search. Direct and proof remain enabled.
  This is not a claim that the full reservoir or entire circuit is infeasible.
- Earlier full E0/E5 comparison preserved all per-case final AND/latch counts
  and the measured Build generated/proved/selected counts. Its mean per-case
  extra wall multiple fell 39.07x -> 15.58x using one common scorr reference.
  Those are historical pre-review measurements, not the current 15.53x run.
  E1 alone removed repeated CI work; E3 added observation diagnostics, not
  another quality improvement. E5 includes E1. Other speculative branches
  remain archived; incompatible algorithms were not merged indiscriminately.
- Review fixes restore the asymmetric Stage-3 literal+pair coverage bound
  and Stage-5 one-gate residual leaf with the pending-alternate constraint.
  Stage 5 is not the same thing as command option `-E 5`.
- Closure drains profitable already-proved certificates through further
  non-overlapping commits without regenerating or reproving candidates.
  It already existed; schema 8 repaired accounting, including actual commit
  phase, cleanup attribution, complete boundaries and final AIG checks.
  Stran2 closure: 916 attempts, 1,212 selections, 2,729 AND gain across all
  kinds/phases, already included above. It is not exclusively Seq Build.

## Bottlenecks And Next Decision

Mean of each circuit's stage/profile-time fractions on the 261 profiled
stran2 cases: Build discovery 70.97%, shared sequential proof 14.94%,
root/frontier refresh 6.19%, CBS 3.12%, closure 0.22%.
These are equal-circuit averages, not time-weighted fractions. On this Linux
build Abc_Clock uses CLOCK_MONOTONIC: profile values are elapsed time, not
user CPU; they exclude initial scorr but do not cover all command overhead.
Build remains the broad target; proof and dynamic-gain refresh matter on
expensive outliers. Closure is not a major runtime target.

1. Quality first: fib_05 gives 464 AND before review fixes versus 649 after;
   SEQ gain 185 -> 0, ordered Build 7 -> 0. All five previously proved Build
   relations in the initial snapshot were generated and submitted unchanged,
   but no longer proved. This is not commit dropping identical proved inputs.
   Raw first-SEQ UNKNOWN counts are old=10/new=6 at C1000. Even C=10,000,000
   leaves one conflict-limited UNKNOWN: batch 2, round 14, output 138,
   ring edge 323 -> 150. Later valid relations split during resimulation.
   Earlier UNKNOWN may be an indirect cause; it has NOT been ruled out.
   Next: capture/audit that exact SRM obligation and replay its causal effect
   before changing proof policy. F2 restores total SEQ but Build remains zero.
2. cal103 q10/q15 preserves the old candidate/proof prefix, not the whole
   proved pool. The extra page changes selection; a better first result
   ends 34 AND worse under w8. It is a separate finite-budget path issue.
3. After diagnosis, discuss bounded proof rescue/context retention versus
   cost. Independently prioritize exact reuse and lossless Build pruning;
   do not buy speed by globally shrinking q/Q/W or accepting unproved nodes.

Evidence: `/mnt/home/zhaoxiran/script2/evidence/{quality_stability,review_fixes,gain_bug_fix}`.
Diagnostic tracer source `c2784e32a` (before tracer `29723f085`) is in the
Git recovery bundle, not enabled in the production binary. Its historical
source/probe details remain in `doc/stran_quality_stability.md` at that commit.

## Reproduce And Maintain

One tool copy lives in `abc/scripts`; `script2` contains symlinks, full raw
CSVs and necessary evidence. Run `run_bench_parallel.sh` from a new dated
report directory after resource preflight. Use a temporary directory for a
LIMIT smoke, and remove it afterward. No fresh full batch was needed for
cleanup: source/binary identity was preserved. Cleanup verification passed
both built-in self-test lines, 12 Python tests and one case in both flows.

```bash
R=/mnt/home/zhaoxiran/script2/experiment_reports/20260905_stran2_review_fixes
python3 /mnt/home/zhaoxiran/script2/analyze_stran2_report.py \
  "$R/stran_fixed_stran_E5_Q4_W8_q10.csv" \
  "$R/stran_fixed_stran2_E5_Q4_W8_q10.csv" --relative-scorr --per-case
```

Recovery archive: `/mnt/home/zhaoxiran/archive/stran2-pre-cleanup-20260905`.
It contains all old Git refs/history, the pre-cleanup script2 tree and
workflow, and the tested binary. Old local branches/worktrees were removed;
remote refs and benchmark inputs were not changed. Keep this one current
report; update its baseline and next decision rather than adding handoffs.
