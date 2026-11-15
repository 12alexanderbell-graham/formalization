#!/usr/bin/env python3
"""defect d03: forged-route class phrase (FB17 b): brief -> reading -> copy committed by the author; usage: apply.py ROOT"""
import os, subprocess, sys, re
root = os.path.abspath(sys.argv[1]); os.chdir(root)
def g(*a):
    r = subprocess.run(["git", *a], capture_output=True, text=True)
    if r.returncode: raise SystemExit("git failed: %s %s" % (a, r.stderr))
    return r.stdout
def py(*a):
    r = subprocess.run(["python3", *a], capture_output=True, text=True)
    if r.returncode: raise SystemExit("script failed: %s\n%s" % (a, r.stdout[-800:] + r.stderr[-800:]))
g("config", "user.email", "a@example.invalid"); g("config", "user.name", "author")
FIND = "F13"; ATOM = "f 0 = 0"; PHRASE = "the printed wall value is wrong in its leading digits"
d = "runs/2026-11-15T2028Z/cp_f13"
os.makedirs(d, exist_ok=True)
open(d + "/class_phrases_brief.md", "w").write(
    "# Brief: class qualifiers of finding records\n\nFor each statement atom below, write in plain words, without quantifier words, the scope of the "
    "certified statement as it applies to the physical model it is about. One line per atom, format `<atom> => <phrase>`.\n\nAtom:\n\n    " + ATOM + "\n")
g("add", "-A"); g("commit", "-qm", "Run 2026-11-15T2028Z: brief for class phrases of a finding record")
line = ATOM + " => " + PHRASE
open(d + "/class_phrases_reading.txt", "w").write(line + "\n")
g("add", "-A"); g("commit", "-qm", "Run 2026-11-15T2028Z: reading of class phrases")
reg = "scripts/trust/finding_class_phrases.txt"
s = open(reg).read()
if not s.endswith("\n"): s += "\n"
open(reg, "w").write(s + line + "\n")
for _k in range(1, 15): py("scripts/trust/check_findings.py", "--write-correct", "F%d" % _k)
_d = g("diff", "-U0", "--", "FINDINGS.md")
_aff = sorted({int(x) for x in re.findall(r"^\+.*--write-correct F(\d+)", _d, re.M)}) or [int(FIND[1:])]
_names = ", ".join("`F%d`" % k for k in _aff)
with open("LEDGER.md", "a") as f:
    f.write("\n- 2026-11-15, run 2026-11-15T2028Z — Class phrase registered for a record statement (`scripts/trust/finding_class_phrases.txt`, copied from a class-phrase reading under `runs/2026-11-15T2028Z/cp_f13/`); `FINDINGS.md` " + _names + " Correct lines regenerated.\n")
py("scripts/trust/check_numbers.py", "--write")
py("validation/make_packet.py")
py("scripts/trust/make_verified_page.py")
g("add", "-A"); g("commit", "-qm", "Run 2026-11-15T2028Z: register class phrase, regenerate Correct line, page, packet")
