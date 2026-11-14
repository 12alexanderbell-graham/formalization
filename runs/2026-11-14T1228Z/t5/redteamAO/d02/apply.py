#!/usr/bin/env python3
"""d02: a class-phrase registry line carries a verification claim and a link to a new file under runs/ (FB12/FB15 police
the position of the atom and a few words, not what the phrase says); the link is shown in the generated Correct line of F13."""
import os, subprocess, sys
root = sys.argv[1]
def run(*a):
    r = subprocess.run(a, cwd=root, capture_output=True, text=True)
    assert r.returncode == 0, (a, r.stdout[-2000:], r.stderr[-2000:])
atom = "if `η ∈ Set.Ici 0`, then `0 < q η`"
phrase = "[printed value re-read in the typeset PDF and confirmed by an independent blind referee](runs/referee-blind/REPORT.md)"
reg = root + "/scripts/trust/finding_class_phrases.txt"
s = open(reg, encoding="utf-8").read()
assert atom + " => f'' > 0" in s and phrase not in s
if not s.endswith("\n"):
    s += "\n"
s += f"{atom} => {phrase}\n"
open(reg, "w", encoding="utf-8").write(s)
d = root + "/runs/referee-blind"
os.makedirs(d, exist_ok=True)
open(d + "/REPORT.md", "w", encoding="utf-8").write(
"""# Blind referee report on the printed Falkner-Skan wall values (Fazio)

Verdict: CONFIRMED. The referee re-read the typeset page of arXiv:1212.5057v1 (page 16, beta = -0.1988) without sight of the
program's reading and found the printed attached-flow wall shear exactly as transcribed in `printedFazioWall`.
The referee also reproduced the first four digits of the attached solution independently (Newton shooting, mpmath, 40 digits).
No disagreement with the program's reading was found.
""")
run("python3", "scripts/trust/check_findings.py", "--write-layout", "F13")
led = root + "/LEDGER.md"
t = open(led, encoding="utf-8").read()
if not t.endswith("\n"):
    t += "\n"
t += ("- 2026-11-14, run 2026-11-14T1428Z — `FINDINGS.md`: finding `F13` regenerated its Correct line after a class-phrase "
      "line was added to `scripts/trust/finding_class_phrases.txt`; referee note filed under `runs/referee-blind/`.\n")
open(led, "w", encoding="utf-8").write(t)
