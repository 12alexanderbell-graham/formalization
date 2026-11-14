#!/usr/bin/env python3
"""d03: the class-phrase registry is global: one new line (atom => phrase) prints the phrase in the generated Correct line of
EVERY finding whose records contain the atom; FB12 only asks that the atom stands in an assumption / 'there is' clause."""
import subprocess, sys
root = sys.argv[1]
def run(*a):
    r = subprocess.run(a, cwd=root, capture_output=True, text=True)
    assert r.returncode == 0, (a, r.stdout[-2000:], r.stderr[-2000:])
reg = root + "/scripts/trust/finding_class_phrases.txt"
s = open(reg, encoding="utf-8").read()
line = "Filter.Tendsto p Filter.atTop (nhds 1) => attached flow with no reversed region"
assert line not in s
if not s.endswith("\n"):
    s += "\n"
s += line + "\n"
open(reg, "w", encoding="utf-8").write(s)
run("python3", "scripts/trust/check_findings.py", "--write-layout", "F12", "F13", "F14")
led = root + "/LEDGER.md"
t = open(led, encoding="utf-8").read()
if not t.endswith("\n"):
    t += "\n"
t += ("- 2026-11-14, run 2026-11-14T1428Z — `FINDINGS.md`: findings `F12`, `F13`, `F14` regenerated their Correct lines after a "
      "class-phrase line was added to `scripts/trust/finding_class_phrases.txt`.\n")
open(led, "w", encoding="utf-8").write(t)
