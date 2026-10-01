#!/usr/bin/env python3
"""Run the frozen pair/full-cut diagnostic on a packaged first-SEQ input."""
import argparse
import json
from pathlib import Path
import sys

PACKAGE = Path(__file__).resolve().parent
sys.path.insert(0, str(PACKAGE / "seq_cut_image"))
from diagnose import diagnose  # noqa: E402


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--mode", choices=("pair", "full"), required=True)
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    manifest = json.loads((PACKAGE / "cases.json").read_text())
    row = next((case for case in manifest["cases"] if case["file"] == args.case), None)
    if row is None:
        parser.error(f"unknown case: {args.case}")
    source = PACKAGE / row["first_seq_path"]
    case = {
        "file": row["file"],
        "input": str(source),
        "input_sha256": row["first_seq_sha256"],
        "source_and": row["loaded_AND"],
        "input_and": row["first_seq_AND"],
    }
    args.out.mkdir(parents=True, exist_ok=False)
    diagnose(case, args.out, args.solver, args.mode)


if __name__ == "__main__":
    main()
