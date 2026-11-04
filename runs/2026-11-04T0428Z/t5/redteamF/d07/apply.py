import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

sub("FINDINGS.md", "7/2 q₀⁴ should be 7/8 q₀⁴\n", "7/2 q₀⁴ should be 7/4 q₀⁴\n")
sub("FINDINGS.md", "(7/8)q₀⁴; D⁰…D³ and every other D⁴ term are right. Printed − true = (21/8)q₀⁴.",
    "(7/4)q₀⁴; D⁰…D³ and every other D⁴ term are right. Printed − true = (7/4)q₀⁴.")
sub("FINDINGS.md", "has one wrong fraction (7/2 instead of 7/8)", "has one wrong fraction (7/2 instead of 7/4)")
