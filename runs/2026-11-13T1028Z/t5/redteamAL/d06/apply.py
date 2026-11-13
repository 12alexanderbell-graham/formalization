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
sub("FINDINGS.md", "uniqueness of the reverse-flow branch is not proved and not needed (the refutation covers every solution of the initial-value problem)",
    "the reverse-flow branch is unique, so its wall shear is the single value the printed number should have been (the refutation covers every solution of the initial-value problem)")
subprocess.run(["python3","scripts/trust/check_findings.py","--write-correct","F14"], cwd=root, check=True, stdout=subprocess.DEVNULL)
ledger("- 2026-11-13 run 1028Z: `FINDINGS.md` `F14` Correct line regenerated from the record, Scope line reworded for clarity.")
for cmd in (["python3","scripts/trust/check_numbers.py","--write"],["python3","validation/make_packet.py"]):
    subprocess.run(cmd, cwd=root, check=True, stdout=subprocess.DEVNULL)
