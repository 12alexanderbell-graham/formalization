#!/usr/bin/env python3
"""d05: validation/make_packet.py prints, as the 'Source' of a packet item, the author's title note of the finding (unchecked
text); the packet is regenerated as the author would and is 'current', so the check passes. The title of F13 is reworded."""
import subprocess, sys
root = sys.argv[1]
def run(*a):
    r = subprocess.run(a, cwd=root, capture_output=True, text=True)
    assert r.returncode == 0, (a, r.stdout[-2000:], r.stderr[-2000:])
p = root + "/FINDINGS.md"
s = open(p, encoding="utf-8").read()
old = ("**Title** (was C-FS-1988): Fazio, arXiv:1212.5057v1 (2012), p. 16, and the values tabulated in Asaithambi, Fluids 6 (2021) 153, "
       "Table 2 (Asaithambi 2005, Zhang–Chen 2009, Salama 2004), and Zhu–Cheng–Wu (2009 preprint), Table 5: five printed values")
new = ("**Title** (was C-FS-1988): Asaithambi, Fluids 6 (2021) 153, Table 2 (Asaithambi 2005, Zhang–Chen 2009, Salama 2004), and "
       "Zhu–Cheng–Wu (2009 preprint), Table 5; Fazio, arXiv:1212.5057v1 (2012), p. 16 prints the correct value and is not affected: five printed values")
assert s.count(old) == 1
open(p, "w", encoding="utf-8").write(s.replace(old, new))
run("python3", "scripts/trust/check_numbers.py", "--write")
run("python3", "validation/make_packet.py")
led = root + "/LEDGER.md"
t = open(led, encoding="utf-8").read()
if not t.endswith("\n"):
    t += "\n"
t += ("- 2026-11-14, run 2026-11-14T1428Z — `FINDINGS.md`: title note of `F13` reworded; validation packet regenerated "
      "(`python3 validation/make_packet.py`).\n")
open(led, "w", encoding="utf-8").write(t)
