#!/usr/bin/env python3
"""Re-audit retained artifacts without rerunning or altering the raw attempts."""
import json
from pathlib import Path
import sys
from check_stran_consolidation import aig_structure_sha

root = Path(sys.argv[1])
raw = json.loads((root/"results.json").read_text())
arms = ("control", "exact", "cache", "factor", "speed")
audit = {}
for name, results in raw.items():
    row = {}
    for arm in arms:
        data = (root/name/(arm+"-after.aig")).read_bytes()
        header = list(map(int, data.split(b"\n", 1)[0].split()[1:]))
        row[arm] = dict(
            structure=aig_structure_sha(root/name/(arm+"-after.aig")),
            loaded=aig_structure_sha(root/name/(arm+"-loaded.aig")),
            ands=header[4], registers=header[2],
            dsec=results[arm]["dsec"], seconds=results[arm]["wall_seconds"])
    row["exact_identity"] = all(row[a]["structure"] == row["control"]["structure"]
                                for a in ("exact", "cache"))
    row["loaded_identity"] = len({row[a]["loaded"] for a in arms}) == 1
    audit[name] = row
passed = all(r["exact_identity"] and r["loaded_identity"] and
             all(r[a]["dsec"] == "PASS" for a in arms) for r in audit.values())
summary = dict(status="PASS" if passed else "FAIL", cases=len(audit), results=audit,
               note="Binary AIG header/latch/output/AND bytes compared; timestamp comments excluded. Raw hashes and attempts preserved.",
               totals={a: dict(ands=sum(r[a]["ands"] for r in audit.values()),
                               seconds=sum(r[a]["seconds"] for r in audit.values()),
                               dsec_pass=sum(r[a]["dsec"] == "PASS" for r in audit.values()))
                       for a in arms})
(root/"structural-audit.json").write_text(json.dumps(summary, indent=2))
print(json.dumps({k: v for k, v in summary.items() if k != "results"}, indent=2))
raise SystemExit(0 if passed else 1)
