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
sub("FINDINGS.md", "for parameters between the separation value and 0 a zero-wall-shear solution with an algebraic tail exists, so the caption is false only in the classical class (exponential approach), the class in which the paper calls the solution unique.",
    "the caption is false for every zero-wall-shear solution of the equation, whatever the tail of the solution (exponential or algebraic): no such solution has the printed parameter.")
ledger("- 2026-11-13 run 1028Z: `FINDINGS.md` `F12` Scope line reworded for clarity.")
for cmd in (["python3","scripts/trust/check_numbers.py","--write"],["python3","validation/make_packet.py"]):
    subprocess.run(cmd, cwd=root, check=True, stdout=subprocess.DEVNULL)
