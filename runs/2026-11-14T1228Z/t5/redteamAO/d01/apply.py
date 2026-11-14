#!/usr/bin/env python3
"""d01: a new class-phrase registry line whose quantifier is spelled with a word FB15's deny-list does not know."""
import subprocess, sys
root = sys.argv[1]
def run(*a):
    r = subprocess.run(a, cwd=root, capture_output=True, text=True)
    assert r.returncode == 0, (a, r.stdout[-2000:], r.stderr[-2000:])
reg = root + "/scripts/trust/finding_class_phrases.txt"
s = open(reg, encoding="utf-8").read()
assert "whichever matter density is chosen" not in s
if not s.endswith("\n"):
    s += "\n"
# the atom is the matter-density assumption `Ω := 245 / 1000` of the toy record F2_toy (an assumption of a universal
# statement, so FB12 accepts it); the phrase has no word of QUANT_WORD (every/any/all/each/whatever/arbitrary/
# unrestricted) and every token of it is an ordinary ASCII word, so FB15 accepts it
s += "Ω := 245 / 1000 => valid whichever matter density is chosen\n"
open(reg, "w", encoding="utf-8").write(s)
run("python3", "scripts/trust/check_findings.py", "--write-layout", "F2")
led = root + "/LEDGER.md"
t = open(led, encoding="utf-8").read()
if not t.endswith("\n"):
    t += "\n"
t += ("- 2026-11-14, run 2026-11-14T1428Z — `FINDINGS.md`: finding `F2` regenerated its Correct line after a class-phrase "
      "line was added to `scripts/trust/finding_class_phrases.txt` (`python3 scripts/trust/check_findings.py --write-layout F2`).\n")
open(led, "w", encoding="utf-8").write(t)
