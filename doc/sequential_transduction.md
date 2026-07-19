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

This is sound but conservative.  The current prototype uses a complete
combinational-TFO local miter whose affected RI boundaries are included as
proof outputs; `-f` optionally shadows it with a whole-design miter.  The
care prefilter is still sampled rather than a formal SODC-care-set SAT query.
It is intended as an auditable reference point for the question “what does
transduction add beyond `&scorr`?”, not as the final scalable algorithm.

## Command line

```
&stran [-FCSTNDGQWKBM num] [-xfvh]
```

- `-F`: BMC/induction depth.
- `-C`: SAT conflict limit per proof obligation.
- `-S`: maximum correspondence refinement rounds (`-1` is unbounded).
- `-T`: maximum exact candidate proofs.
- `-N`: maximum accepted transactions.
- `-D`: existing divisors retained per victim set.
- `-G`: minimum exact `AND + register` gain needed before proof.
- `-Q` / `-W`: 64-bit words and sequential frames in the random signature batch.
- `-K` / `-B`: constructed-candidate limit and construction base pool (`-B 0` is all-pairs).
- `-M`: exactly one or two leaves replaced by one divisor.
- `-x`: toggle constructed one-AND divisors.
- `-f`: whole-miter shadow audit for every accepted local proof.
- `-v`: candidate/proof trace.

For a quick regression from the repository root:

```
bash test/run_stran_regression.sh
```

It runs `&stran` on a small sequential contextual-redundancy example and then
checks the original/result pair with independent `dsec`.

For server experiments:

```
python3 scripts/bench_scorr_then_stran.py \
  --aig-dir <input-aig-dir> --abc ./abc --out results.csv \
  --jobs 64 --timeout 12800 --scorr-args '-F 1 -C 200'
```

The script runs `&scorr` first, then runs `&stran` on the resulting AIG, and
finally runs `dsec`.  Its `stran_extra_and_reduction` CSV column is therefore
the exact extra AND reduction beyond the baseline `&scorr` result.  Override
the search/proof budget directly, for example:

```
python3 scripts/bench_scorr_then_stran.py \
  --aig-dir benchmarks --abc ./abc --out results.csv --jobs 64 --timeout 12800 \
  --stran-args '-M 2 -F 2 -C 5000 -S -1 -T 2000 -N 100 -D 24 -B 64 -K 32 -Q 4 -W 8'
```
