import sys, os
def edit(root, rel, old, new):
    p = os.path.join(root, rel)
    s = open(p, encoding="utf-8").read()
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    open(p, "w", encoding="utf-8").write(s.replace(old, new))
def ledger(root, line):
    p = os.path.join(root, "LEDGER.md")
    s = open(p, encoding="utf-8").read()
    if not s.endswith("\n"): s += "\n"
    open(p, "w", encoding="utf-8").write(s + line + "\n")

root=sys.argv[1]
edit(root,'FINDINGS.md',"- **Correct (inverting the paper's own Eq. (A1)):** (7/8)q₀⁴; D⁰…D³ and every other D⁴ term are right. Printed − true = (21/8)q₀⁴.","- **Correct (inverting the paper's own Eq. (A1)):** (7/4)q₀⁴; D⁰…D³ and every other D⁴ term are right. Printed − true = (7/4)q₀⁴.")
ledger(root,'- 2026-11-13 run 1028Z: `FINDINGS.md` `F3` Correct line reworded for clarity.')
