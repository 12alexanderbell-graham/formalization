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
sub("FINDINGS.md", "η₂₀ ≃ 0.15[src]ε, −0.12[src]ε and η₃₀ ≃ 4[src]ε, −0.18[src]ε at Ω = 0.041[src], 0.25[src]",
    "η₂₀ ≃ 0.15[src]ε, −0.12[src]ε and η₃₀ ≃ 4[src]ε, −0.18[src]ε at Ω = 0.25[src], 0.041[src]")
ledger("- 2026-11-13 run 1028Z: `FINDINGS.md` `F10` Printed line reordered for clarity.")
for cmd in (["python3","scripts/trust/check_numbers.py","--write"],["python3","validation/make_packet.py"]):
    subprocess.run(cmd, cwd=root, check=True, stdout=subprocess.DEVNULL)
