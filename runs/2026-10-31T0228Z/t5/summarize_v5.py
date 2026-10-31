#!/usr/bin/env python3
"""Summarize judge-v5 results into RESULTS.md (run 0228Z)."""
import pathlib, re
H = pathlib.Path(__file__).parent
O = H.parent.parent / "2026-10-31T0028Z" / "t5"
R = H / "results"

def claim(n):
    for d in [H / "ports" / n, (H / "redteamD" / n[1:]) if n[0] == "D" else (O / f"redteam{n[0]}" / n[1:])]:
        c = d / "claim.md"
        if c.exists():
            m = re.search(r"Category:\s*(.*)", c.read_text())
            return m.group(1).strip() if m else "?"
    src = (H / "redteamD" / n[1:]) if n[0] == "D" else (O / f"redteam{n[0]}" / n[1:])
    c = src / "claim.md"
    return re.search(r"Category:\s*(.*)", c.read_text()).group(1).strip() if c.exists() else "?"

rows = []
for f in sorted(R.glob("*.txt")):
    t = f.read_text()
    name = f.stem
    base = re.search(r"base: (\w{7})", t)
    res = re.search(r"RESULT V5 (\w+)(.*)", t)
    n = name.replace("final_", "")
    cat = "control" if n == "control" else claim(n.rstrip("s") if n.endswith("07s") else n)
    if not res:
        rows.append((name, cat, base.group(1) if base else "?", "UNFINISHED", ""))
        continue
    verdict, why = res.group(1), res.group(2).strip()
    fails = ", ".join(k for k, v in re.findall(r"(\w+)=(\d)", why) if v == "1")
    note = ""
    if verdict == "REJECTED" and fails == "map" and "map: FAIL (committed TRUST_MAP.md is stale)" in t:
        verdict, note, fails = "ACCEPTED*", "only the stale map failed; the author regenerates it (judge fixed later)", ""
    rows.append((name, cat, base.group(1) if base else "?", verdict, fails or note))

out = ["# T5 results, judge v5 (run 2026-10-31T0228Z)", "",
       "Judge: `judge_v5.sh` = the CI checks on main at the base commit (Checked + Work build, forbidden tokens, trust step after author relock, certified numbers, frozen and certified-number diffs vs base). Ports (`ports/`) re-apply a 0028Z/D defect to the tagged records. `final_*` = judged at the last check version (a7f5b6a).",
       "", "| Defect | Category | Base | Verdict | Caught by / note |", "|---|---|---|---|---|"]
out += [f"| {a} | {b} | {c} | {d} | {e} |" for a, b, c, d, e in rows]
(H / "RESULTS.md").write_text("\n".join(out) + "\n")
print("\n".join(out))
