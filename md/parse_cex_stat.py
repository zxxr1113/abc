#!/usr/bin/env python3
"""
Parse [CEX-STAT] lines from abc &scorr output and print a summary table.

Usage:
    ./abc -c "read_aiger foo.aig; &get; &scorr; &put" 2>&1 | tee foo.log
    python3 parse_cex_stat.py foo.log

Or pipe directly:
    ./abc -c "read_aiger foo.aig; &get; &scorr; &put" 2>&1 | python3 parse_cex_stat.py -
"""

import sys
import re

PATTERN = re.compile(
    r'\[CEX-STAT\]\s+'
    r'r=\s*(\d+)\s+'
    r'nSrmCi=\s*(\d+)\s+'
    r'nSrmAnd=\s*(\d+)\s+'
    r'nSrmCo=\s*(\d+)\s+'
    r'nRecs=\s*(\d+)\s+'
    r'avgLits=([\d.]+)'
)


def parse_file(fh):
    rows = []
    for line in fh:
        m = PATTERN.search(line)
        if m:
            rows.append({
                'r':       int(m.group(1)),
                'nSrmCi':  int(m.group(2)),
                'nSrmAnd': int(m.group(3)),
                'nSrmCo':  int(m.group(4)),
                'nRecs':   int(m.group(5)),
                'avgLits': float(m.group(6)),
            })
    return rows


def print_table(rows):
    if not rows:
        print("No [CEX-STAT] lines found.")
        return

    hdr = f"{'r':>5}  {'nSrmCi':>8}  {'nSrmAnd':>10}  {'nSrmCo':>8}  {'nRecs':>6}  {'avgLits':>9}  {'litRatio%':>10}"
    print(hdr)
    print('-' * len(hdr))

    total_recs = 0
    total_lits = 0
    for row in rows:
        ci = row['nSrmCi']
        ratio = 100.0 * row['avgLits'] / ci if ci > 0 else 0.0
        print(f"{row['r']:>5}  {ci:>8}  {row['nSrmAnd']:>10}  {row['nSrmCo']:>8}  "
              f"{row['nRecs']:>6}  {row['avgLits']:>9.2f}  {ratio:>10.2f}")
        total_recs += row['nRecs']
        total_lits += row['nRecs'] * row['avgLits']

    print('-' * len(hdr))
    print(f"Rounds: {len(rows)}   total_recs: {total_recs}   "
          f"avg_lits_overall: {total_lits/total_recs:.2f}" if total_recs else "No records.")

    # Extra: cube tightness per round
    ratios = [100.0 * r['avgLits'] / r['nSrmCi'] for r in rows if r['nSrmCi'] > 0]
    if ratios:
        print(f"Lit/CI ratio — min: {min(ratios):.2f}%  max: {max(ratios):.2f}%  avg: {sum(ratios)/len(ratios):.2f}%")


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else '-'
    if path == '-':
        rows = parse_file(sys.stdin)
    else:
        with open(path) as fh:
            rows = parse_file(fh)
    print_table(rows)


if __name__ == '__main__':
    main()
