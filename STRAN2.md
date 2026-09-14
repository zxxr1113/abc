# `&stran2` development guide

This file is the single source of truth for the current implementation and
latest measurements. Historical exploration notes are intentionally omitted.

## Current state

- Production tree: `/mnt/home/zhaoxiran/abc`
- Branch: `codex/stran2`
- Integrated feature commit: `55e476c65c6c29a26399e8e8c63566f972867de6`
- That commit's measured binary SHA256:
  `cabea113620f6788af16ebfce2c95b64b39ddc674e3ca550fa626a4fabaaaed6`
- Module-refactor validation binary SHA256:
  `a19f03ddc156795692ff41e9a3bd5548979a2d6fff349164774e17e8fc93ceab`
- Build: `make ABC_USE_NO_READLINE=1 -j8`

`&stran2` now applies `-F/-C` uniformly to its initial integrated `scorr` and
to every later transaction proof. The no-option `&stran2` default remains
F1/C1000. `&stran` keeps its F1/C100 default.

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

- `20260913_stran2_internal_scorr_*`: Fast35 F/C matrix
- `20260914_stran2_frame_quick268_*`: Quick268 frame attribution

Supporting launch records and audits:

- `/mnt/home/zhaoxiran/script2/evidence/stran2_scorr_fc/20260913`
- `/mnt/home/zhaoxiran/script2/evidence/stran2_frame_attribution/20260914`

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
