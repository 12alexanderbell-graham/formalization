import glob, os, re, sys
R = sys.argv[1] if len(sys.argv) > 1 else "/home/claude/t5/results"
rows = []
for t in "ABC":
    for d in sorted(glob.glob(f"/home/claude/t5/redteam{t}/d0*")):
        n = os.path.basename(d); key = t + n
        f = f"{R}/{key}_v2.txt" if os.path.exists(f"{R}/{key}_v2.txt") else f"{R}/{key}.txt"
        if not os.path.exists(f): continue
        txt = open(f).read()
        cat = re.search(r"Category:\s*(.*)", open(f"{d}/claim.md").read()).group(1).strip()
        bef = "ACCEPTED" if ("RESULT BEFORE ACCEPTED" in txt or "RESULT ACCEPTED" in txt) else ("INVALID?" if "build: FAIL" in txt else "caught")
        aft = "ACCEPTED" if "RESULT AFTER ACCEPTED" in txt else ("n/a" if "RESULT AFTER" not in txt else ("INVALID?" if "build: FAIL" in txt else "caught"))
        why = ""
        m = re.search(r"RESULT AFTER REJECTED (.*)", txt)
        if m: why = m.group(1)
        rows.append((key, cat, bef, aft, why))
for r in rows: print("| " + " | ".join(r) + " |")
