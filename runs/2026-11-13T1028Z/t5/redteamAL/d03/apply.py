import sys, subprocess
import sys, re
root = sys.argv[1]
def rd(p): return open(f"{root}/{p}", encoding="utf-8").read()
def wr(p, t): open(f"{root}/{p}", "w", encoding="utf-8").write(t)
def sub(p, old, new):
    t = rd(p); assert t.count(old) == 1, (p, old[:40], t.count(old)); wr(p, t.replace(old, new))
def ledger(line):
    t = rd("LEDGER.md")
    if not t.endswith("\n"): t += "\n"
    wr("LEDGER.md", t + line + "\n")
sub("FINDINGS.md", "Lean covers the flat instance only; the curved statement is sympy + Milne + open-dust Mattig checks (referee).",
    "Lean covers the sign for every curvature K, flat or curved; the sympy + Milne + open-dust Mattig checks (referee) agree.")
ledger("- 2026-11-13 run 1028Z: `FINDINGS.md` `F4` Scope line reworded for clarity.")
for cmd in (["python3","scripts/trust/check_numbers.py","--write"],["python3","validation/make_packet.py"]):
    subprocess.run(cmd, cwd=root, check=True, stdout=subprocess.DEVNULL)
