#!/usr/bin/env python3
"""Authenticate surviving historical bytes only. Never search or call a solver."""
import argparse
from common import *

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    require(not args.out.exists(), 'new authentication output required')
    rows = []
    for case in CASES:
        frozen, candidates, snapshot, bindings = authenticate(case)
        rows.append(dict(case=case, snapshot=str(snapshot), input_sha256=frozen['input_sha256'],
                         initial256_sha256=frozen['arms']['A']['free_domain_sha256'],
                         sequence_sha256=frozen['sequence_sha256'], roots=32,
                         baseline_candidates=len(candidates), files=bindings.files,
                         missing_files=[], changed_files=[], status='PASS'))
    write_new(args.out, dict(schema=1, original_review_sha256=REVIEW_SHA256, cases=rows,
                             action='hash-only historical evidence authentication',
                             solver_calls=0, searches=0, original_evidence_modified=False))
if __name__ == '__main__':
    main()
