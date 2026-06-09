# Failed-endpoint TFO experiment analysis

Branch: `incre_sim_seed`

This note explains why the uploaded `-I` runs issue many more SAT calls even
though they finish in fewer outer refinement iterations.

## Observed result

For `ILA_Flute_BGEU_problem`:

| mode | iterations | SAT calls | real CEX | simulation splits |
| --- | ---: | ---: | ---: | ---: |
| `-v -w` | 131 | 2,692,868 | 936,450 | 960,644 |
| `-v -w -I` | 93 | 3,985,757 | 2,418,965 | 888,350 |
| `-v -w -i` | 127 | 2,002,043 | 937,097 | 964,025 |
| `-v -w -i -I` | 95 | 3,543,311 | 2,419,578 | 888,654 |

The additional calls are mainly SAT/disproved outputs, not additional
UNSAT/proved outputs. `-I` leaves more candidates for SAT and processes much
larger SRMs per iteration, so fewer iterations do not imply fewer solver calls.

## Confirmed implementation bug

The previous `-I` path called:

```c
Cec_ManStartSimInfo(vSimInfo, Vec_PtrSize(vSimInfo));
```

This zeroed every PI/timeframe slot. The standard path zeros only initial ROs
and random-fills the PI/timeframe slots.

The first `-I` batch always falls back to full resimulation because the
persistent table is not initialized. It therefore must behave exactly like the
baseline, but the logs already diverge in iteration 1:

| benchmark | baseline simulation splits | `-I` first-fallback splits |
| --- | ---: | ---: |
| BGEU | 2,206 | 1,786 |
| BLT | 2,116 | 1,773 |
| SRAI | 2,177 | 1,790 |
| XORI | 2,136 | 1,789 |

This changes the equivalence classes in the first iteration. Every later SRM,
ring edge, CEX, and SAT-call count then follows a different trajectory.

The fix restores standard initialization for full fallback. Successful local
batches do not initialize the full `vSimInfo` array at all; they only pack CEXes
to obtain `(output, bit)` mappings. If a local batch later requests fallback,
the batch is reloaded after standard initialization.

## What is algorithmic rather than a bug

Full resimulation replays each CEX from sequential inputs and can
opportunistically split classes anywhere affected by that input pattern.
Failed-endpoint TFO simulation intentionally treats the endpoint values as
cut-point updates and only propagates downstream.

Therefore `-I` can legitimately produce fewer simulation splits. Candidates
that baseline simulation removed opportunistically remain for later SAT work.
With rings, splitting a class also creates new adjacent ring pairs, so the next
SRM is not simply the previous SRM minus the failed pairs.

The `-i` option reduces proof scheduling to invalidated TFO/ring pairs, but it
does not make the candidate graph immutable and does not guarantee the same SAT
call count as full simulation.

## Important semantic check

The endpoint literals currently sampled by SAT are the endpoint copies in the
speculatively reduced SRM. They are valid values for the failed SRM output, but
they are not guaranteed to be values of the unreduced original AIG endpoint
under a complete original-network simulation.

The current incremental engine deliberately uses them as authoritative
cut-point values. This is a heuristic simulation pattern, not a replay of the
whole CEX. Its effectiveness must be measured by whether it splits the SAT
failed pairs and useful downstream pairs.

## Added diagnostic

Profiling output now includes:

```text
pending=<count>
```

This is the number of real SAT failed pairs that are still merged immediately
after resimulation.

- `pending` large: the endpoint-value/local-refinement path is failing to split
  pairs that SAT just disproved. Investigate endpoint sampling, phase handling,
  packed-bit conflicts, or TFO evaluation.
- `pending` near zero but SAT calls still rise: the increase mainly comes from
  losing full-CEX opportunistic splits and from changed class/ring topology.

The counter was already computed by `Gia_ManCheckRefinements`; exposing it adds
no additional graph traversal.

## Next experiment

Rebuild and rerun the four no-skip modes. The first full-fallback iteration of
baseline and `-I` should now have identical simulation split counts. Only after
that invariant holds should later `pending`, per-iteration SRM size, and total
SAT calls be used to judge the failed-endpoint TFO design.
