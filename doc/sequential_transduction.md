# `&stran`: proof-gated sequential transduction

`&stran` is an experimental ABC9 command for finding area reductions that
ordinary `&scorr` does not *propose*.  It is deliberately independent of
`&sodc` and never invokes the `&scorr` command as a pre- or post-pass.
Instead, it reuses `Cec_ManLSCorrespondence`, the BMC plus induction/refinement
infrastructure below `&scorr`, as a proof oracle for each new transaction.

## Search space

For a target AND node `t = f0 & f1`, `&stran` selects one fanin `fi` and
speculatively replaces it with either:

1. a preceding existing literal `d`; or
2. a newly constructed one-AND divisor `h = d0 & d1`.

The candidate is duplicated, structurally hashed, normalized, and sequentially
cleaned.  This produces the final form of an add-and-remove transduction:
`h` is added in the speculative copy and the old fanin is removed.  Expressing
the final transaction directly is equivalent to materializing the temporary
wire first, but avoids permanently growing the AIG for failed candidates.

Only candidates with a positive exact change in `AND + register` count are
proved.  A divisor must precede the target, which rules out combinational
cycles without a TFO traversal.  After a successful transaction, the command
restarts the search because cleanup changes node IDs and can expose cascades.

This is the key distinction from `&scorr`: correspondence discovers global
relations such as `u == v` or `u == !v`; `&stran` explicitly asks whether a
contextual replacement `fi <- h(d0,d1)` preserves the sequential behavior.
The constructed `h` is not required to be globally equivalent to `fi`.

## Proof and soundness boundary

For each candidate, `&stran` builds a sequential miter between the current GIA
and the speculative GIA.  It configures `Cec_ManLSCorrespondence` with the
same `-F`, `-C`, and `-S` parameters used by the signal-correspondence engine.
It commits only if every miter output is reduced to constant zero.  A SAT
counterexample, an unresolved correspondence, or a conflict-limited timeout
therefore rejects the candidate; it never changes the current network.

This is sound but conservative.  The current prototype uses a whole-design
sequential miter, not the TCAD paper's local TFO window and explicit
SODC-care-set SAT query.  It is intended as an auditable reference point for
the question “what does transduction add beyond `&scorr`?”, not as the final
scalable algorithm.  The next research step is to retain this transaction
interface while replacing the coarse prefilter/oracle with windowed,
counterexample-guided SODC checks.

## Command line

```
&stran [-FCSTNDG num] [-xvh]
```

- `-F`: BMC/induction depth.
- `-C`: SAT conflict limit per proof obligation.
- `-S`: maximum correspondence refinement rounds (`-1` is unbounded).
- `-T`: maximum exact candidate proofs.
- `-N`: maximum accepted transactions.
- `-D`: preceding divisors examined per target fanin.
- `-G`: minimum exact `AND + register` gain needed before proof.
- `-x`: toggle constructed one-AND divisors.
- `-v`: candidate/proof trace.

For a quick regression from the repository root:

```
bash test/run_stran_regression.sh
```

It runs `&stran` on a small sequential contextual-redundancy example and then
checks the original/result pair with independent `dsec`.

For server experiments:

```
bash scripts/run_stran_bench.sh <input-aig-dir> <result-dir> ./abc
bash scripts/verify_stran_results.sh <input-aig-dir> <result-dir> ./abc
```

Set `STRAN_ARGS` to override the command's proof/search budget, for example:

```
STRAN_ARGS='-F 2 -C 5000 -S -1 -T 2000 -N 100 -D 24' \
  bash scripts/run_stran_bench.sh benchmarks results ./abc
```
