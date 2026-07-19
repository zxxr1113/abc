# Sequential transduction profiling

## Command

`&stran -p` prints two machine-readable summary lines after the normal result:

```text
Sequential transduction profile: total=... sim=... care=... spec=... existing=... construct=... gain=... other=... sec.
Sequential transduction proof profile: retain=... miter=... corr=... final=... miter=... corr=... shadow=... time=... sec.
```

The counters in parentheses are invocation counts.  `gain` includes speculative add/final duplication,
cleanup, and exact gain computation.  `corr` is the time inside `Cec_ManLSCorrespondence`; `miter` is local
TFO miter construction.  `other` is uninstrumented control, supergate collection, deallocation, and commit
overhead.  Profiling uses ABC's internal clock and does not include the later independent `dsec` audit.

## Current CSV diagnosis

The uploaded `scorr_then_stran.csv` contains 343 rows, but only 154 complete `&scorr -> &stran -> dsec` PASS
rows.  Another 183 rows are `BrokenProcessPool` records caused by terminating the parallel run, and six become
combinational after `&scorr`, which the current `&stran` deliberately rejects.

For the 154 valid rows:

- 90 have a positive extra AND/latch reduction, but the weighted extra AND reduction is only 0.083%;
- the median per-case extra AND reduction is 0.016%;
- 151 cases reach the global `T=1000` proof limit;
- 152089 positive-gain candidates are formally tried and only 499 are accepted (0.328%);
- 95572 fail/unresolve retention and 56018 fail/unresolve the final-network proof;
- aggregate `&stran` time is about 1050 times aggregate `&scorr` time.

This points to candidate ordering/filtering and repeated formal proof as the first bottleneck, not a shortage of
generated candidates.

## Representative cases

| Case | Why profile it |
|---|---|
| `bitlevel/safety/2020/mann/simple_alu.aig` | extreme fast success: 83 -> 1 AND after `&scorr`, 82 extra ANDs |
| `bitlevel/safety/2019/beem/bakery.3.prop1-func-interl.aig` | small typical success: 6 extra ANDs, 4 accepted transactions |
| `bitlevel/safety/2019/beem/collision.1.prop1-func-interl.aig` | medium success: 30 extra ANDs but about 80 seconds |
| `bitlevel/safety/2019/beem/exit.3.prop1-back-serstep.aig` | removal-proof pathology: 999 final-unproved, only 1 extra AND |
| `bitlevel/safety/2019/beem/pgm_protocol.8.prop6-func-interl.aig` | zero-gain expensive case: 1000 proofs and no accepted transaction |
| `bitlevel/safety/2024/hkust/x-epic/xepic_a12.aig` | largest absolute win: 1102 extra ANDs, but 100 accepted transactions and high runtime |

Start with `T=200` and `N=20` so profiling finishes quickly.  For one case, from the ABC repository root:

```bash
bench_root=/absolute/path/to/all_test/all
case_rel=bitlevel/safety/2019/beem/collision.1.prop1-func-interl.aig
case_tag=collision
mkdir -p profiles/$case_tag
./abc -q "&read $bench_root/$case_rel; &write profiles/$case_tag/base.aig; &scorr -F 1 -C 200; &write profiles/$case_tag/scorr.aig; &stran -M 1 -F 1 -C 1000 -S -1 -T 200 -N 20 -D 32 -B 64 -K 32 -Q 4 -W 8 -p; &write profiles/$case_tag/final.aig" 2>&1 | tee profiles/$case_tag/run.log
./abc -q "dsec profiles/$case_tag/base.aig profiles/$case_tag/final.aig" 2>&1 | tee -a profiles/$case_tag/run.log
```

Repeat by changing only `case_rel` and `case_tag`.  Do not add `-f` during profiling because whole-miter shadow
time would obscure the production path; the final `dsec` remains mandatory.
