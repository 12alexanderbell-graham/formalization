#!/usr/bin/env python3
"""d03: a second '### F2' section placed before the real one. The rules key sections by 'F<k>' in dicts (the later
section wins), so FB7/FB9/FB10 read only the real F2; the first one has hand-written 'generated' lines."""
import re, subprocess, sys
from pathlib import Path

root = Path(sys.argv[1])
p = root / "FINDINGS.md"
t = p.read_text(encoding="utf-8")

i = t.index("### F2 (was C4).")
j = t.index("### F3 (was C3).")
real = t[i:j]
lines = real.split("\n")
heading = lines[0]
printed = next(l for l in lines if l.startswith("- **Printed (generated"))
correct = next(l for l in lines if l.startswith("- **Correct (generated"))
marker = next(l for l in lines if l.startswith("- **Unchecked notes**"))

# the real section keeps only F2_error in its block; the first one takes F2_toy
assert real.count("<!-- certified: F2_toy F2_error -->") == 1
new_real = real.replace("<!-- certified: F2_toy F2_error -->", "<!-- certified: F2_error -->")

# the first section: same text, but the reader's description names Eq. (21) instead of Eq. (22)
fake_heading = heading.replace("Eq. (22)", "Eq. (21)")
assert fake_heading != heading
fake_printed = printed.replace("Eq. (22), p. 4. Printed:", "Eq. (21), p. 4. Printed:")
assert fake_printed != printed
fake = "\n".join([
    fake_heading,
    fake_printed,
    correct.replace("`F2_error` (for every data meeting its hypotheses): the value derived in Lean `cosmoCoeff 5 a t₀` lies above the printed value `printedCLSL0 (3 / 10) w₀ (-1 / 2)`, by the difference certified below",
                    "`F2_toy` (for every data meeting its hypotheses): the certified values below")
    if False else
    "- **Correct (generated from the Lean records by `python3 scripts/trust/check_findings.py --write-correct F2`; do not edit):** "
    "`F2_toy` (for every data meeting its hypotheses): the certified values below.",
    "<!-- certified: F2_toy -->",
    "<!-- /certified -->",
    marker,
    "  - *(author)* **Classification:** Source error (misprint); see the section below.",
    "",
    "",
])
t = t[:i] + fake + new_real + t[j:]
p.write_text(t, encoding="utf-8")

# regenerate blocks, then the layout of the real F2, as an author would
subprocess.run([sys.executable, "scripts/trust/check_numbers.py", "--write"], cwd=root, check=True, stdout=subprocess.DEVNULL)
subprocess.run([sys.executable, "scripts/trust/check_findings.py", "--write-layout", "F2"], cwd=root, check=True,
               stdout=subprocess.DEVNULL)

led = root / "LEDGER.md"
s = led.read_text(encoding="utf-8")
if not s.endswith("\n"):
    s += "\n"
s += "- 2026-11-13, run 2026-11-13T1828Z — `FINDINGS.md` `F2`: certified blocks regrouped (one block per record).\n"
led.write_text(s, encoding="utf-8")
