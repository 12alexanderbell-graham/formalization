#!/usr/bin/env python3
"""Table of judge-v6 results (run 1028Z): results/*.txt -> stdout (markdown)."""
import re, sys
from pathlib import Path
R = Path(__file__).parent
CLAIMS = {"Ad03": "../../2026-10-31T0028Z/t5/redteamA/d03", "Ad04": "../../2026-10-31T0028Z/t5/redteamA/d04",
          "Ad05": "../../2026-10-31T0028Z/t5/redteamA/d05", "Bd04": "../../2026-10-31T0028Z/t5/redteamB/d04",
          "Dd01": "../../2026-10-31T0228Z/t5/redteamD/d01", "Dd04": "../../2026-10-31T0228Z/t5/redteamD/d04",
          "Dd04p": "ports/Dd04"}
print("| Defect | Base | Category | Verdict | Caught by |\n|---|---|---|---|---|")
for f in sorted(R.glob("results/*.txt")):
    t = f.read_text(); n = f.stem
    base = (re.search(r"base: ([0-9a-f]{7})", t) or [None, "?"])[1]
    d = R / CLAIMS.get(n, f"redteamE/d{n[2:]}" if n.startswith("Ed") else "none")
    cat = ""
    if (d / "claim.md").exists():
        m = re.search(r"Category:\s*(.*)", (d / "claim.md").read_text()); cat = m.group(1).strip() if m else ""
    res = re.findall(r"RESULT (V6 ACCEPTED|V6 REJECTED.*|APPLY_FAILED)", t)
    if not res or (res[-1] == "APPLY_FAILED" and "RESULT V6" not in t):
        v, why = ("APPLY_FAILED" if res else "PENDING"), ""
    else:
        v = "ACCEPTED" if "ACCEPTED" in res[-1] else "REJECTED"
        why = ", ".join(k for k, x in re.findall(r"(\w+)=(\d)", res[-1]) if x == "1")
        # in v6 the 'relock' step also runs check_prose --base: with prose=1 it is the same finding
        if "prose" in why: why = why.replace("relock, ", "")
        if "APPLY_FAILED" in res: v, why = "NOT JUDGED (apply failed on the current tree)", ""
    print(f"| {n} | {base} | {cat} | {v} | {why} |")
