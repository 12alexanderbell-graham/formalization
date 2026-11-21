#!/usr/bin/env python3
"""Score writers SN, SN2, SN3 against scripts/trust/check_stale_necessity.py as it stands (after this run's S-N4/S-N5)."""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/trust"))
import check_stale_necessity as c
trust = c.parse_trust((ROOT / "TRUST_MAP.md").read_text(encoding="utf-8"))
for tag, f in (("SN", "runs/2026-11-20T2028Z/t5/writer_SN.json"), ("SN2", "runs/2026-11-21T0228Z/t5/writer_SN2.json"),
               ("SN3", "runs/2026-11-21T0228Z/t5/writer_SN3.json")):
    r = {"num": [0, 0], "desc": [0, 0], "true": [0, 0]}
    for e in json.load(open(ROOT / f)):
        text = "# x\n\n" + (f"## Section on `{e['section_headline']}`\n" if e.get("section_headline") else "") + e["line"] + "\n"
        k = "true" if e["kind"] == "TRUE" else ("num" if e["by_number"] else "desc")
        hit = bool(c.scan(text, trust))
        r[k][0] += hit; r[k][1] += 1
        if hit == (k == "true"):
            print("  ", "FALSE+" if k == "true" else "MISSED", tag, e["id"], e["line"][:120])
    print(f"{tag}: recall by number {r['num'][0]}/{r['num'][1]}, by description {r['desc'][0]}/{r['desc'][1]}, "
          f"false positives {r['true'][0]}/{r['true'][1]}")
