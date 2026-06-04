### 1. Summary
This PR fixes a bug in the `ssw` engine where the `Other` time in `scorr -v` was calculated incorrectly, often resulting in negative values. The fix ensures that `timeBmc` only counts the administrative overhead of the BMC phase, excluding nested SAT and Simulation time.

### 2. Root Cause
In the current implementation, `timeBmc` wraps the entire BMC phase. However, the functions called inside this phase also update the global `timeSat` and `timeSimSat` timers.

**Call Relationship:**
- Ssw_ManSweepBmc (Starts timeBmc)
    - Ssw_NodesAreEquiv (Updates timeSat internally)
    - Ssw_ManResimulate (Updates timeSimSat internally)
- Ssw_ManSweepBmc (Ends timeBmc)

Because the final statistics calculate `Other = Total - SAT - Sim - BMC - Reduce`, the time spent in SAT/Sim during the BMC phase is subtracted twice.

### 3. Comparison (Benchmark Results)
Tested with: `pc_sfifo_3.cil+token_ring.08.cil-2.aig`

**Before Fix (Incorrect):**
```
BMC         =    22.34 sec ( 90.95 %)
Sim SAT     =    13.02 sec ( 53.01 %)
SAT solving =    10.62 sec ( 43.23 %)
Other       =   -21.44 sec (-87.30 %)  <-- LOGICAL ERROR
TOTAL       =    24.56 sec (100.00 %)
```

**After Fix (Corrected):**
```
BMC         =     0.74 sec (  3.18 %)
Sim SAT     =    12.37 sec ( 53.39 %)
SAT solving =     9.93 sec ( 42.85 %)
Other       =     0.11 sec (  0.46 %)  <-- CORRECTED
TOTAL       =    23.17 sec (100.00 %)
```

### 4. Proposed Changes
I redefined the semantics of `timeBmc` to represent "Pure Overhead," matching the existing behavior of `timeReduce`.

In `sswSweep.c` and `sswConstr.c`, the timer update is modified as follows:

```c
abctime clk = Abc_Clock();
abctime timeSatBefore = p->timeSat;
abctime timeSimBefore = p->timeSimSat;

// ... BMC execution logic ...

p->timeBmc += (Abc_Clock() - clk) - (p->timeSat - timeSatBefore) - (p->timeSimSat - timeSimBefore);
```

### 5. Impact
- Resolves the negative time reporting issue in `scorr -v`.
- Maintains consistency across different phase timers in the `ssw` engine.
- No changes to the actual SAT solving or logic, only to the statistical accumulation.

---

