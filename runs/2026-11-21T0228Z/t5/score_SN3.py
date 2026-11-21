#!/usr/bin/env python3
"""Score writer SN3 (brief BRIEF_SN3.md) against sn4_proto.py (as frozen) and scripts/trust/check_stale_necessity.py on the excerpt's headlines."""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_stale_necessity as c
sys.path.insert(0, str(Path(__file__).parent))
import sn4_proto as P4
trust = c.parse_trust((ROOT / "TRUST_MAP.md").read_text(encoding="utf-8"))
d = json.load(open(Path(__file__).parent / "writer_SN3.json"))
rows = []
for e in d:
    text = "# x\n\n"
    if e.get("section_headline"):
        text += f"## Section on `{e['section_headline']}`\n"
    text += e["line"] + "\n"
    got = P4.scan(text, trust)
    old = c.scan(text, trust)
    print(e['id'], 'S-N4' if got else '-', 'main' if old else '-')
    rows.append((e["id"], e["kind"], e.get("by_number"), bool(got), e["line"]))
stale_num = [r for r in rows if r[1] == "STALE" and r[2]]
stale_desc = [r for r in rows if r[1] == "STALE" and not r[2]]
true = [r for r in rows if r[1] == "TRUE"]
print(f"recall (by number): {sum(r[3] for r in stale_num)}/{len(stale_num)}; by description flagged "
      f"{sum(r[3] for r in stale_desc)}/{len(stale_desc)}; false positives {sum(r[3] for r in true)}/{len(true)}")
for r in rows:
    if (r[1] == "STALE" and not r[3]) or (r[1] == "TRUE" and r[3]):
        print(("MISSED " if r[1] == "STALE" else "FALSE+ ") + r[0] + (" (desc)" if not r[2] else "") + ": " + r[4])
