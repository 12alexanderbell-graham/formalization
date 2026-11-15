#!/usr/bin/env python3
"""d01: re-bind candidate C28 (an unformalized, parked claim about Lusso et al. 2019 Sect. 3.2) to the verified
finding F11 through F11's title note (FB22 only compares ids with the '(was ...)' of the title note)."""
import sys
root = sys.argv[1]

def sub1(path, old, new):
    t = open(f"{root}/{path}", encoding="utf-8").read()
    assert t.count(old) == 1, (path, old[:50], t.count(old))
    open(f"{root}/{path}", "w", encoding="utf-8").write(t.replace(old, new))

t = open(f"{root}/FINDINGS.md", encoding="utf-8").read()
lines = t.split("\n")
idx = [i for i, l in enumerate(lines) if l.startswith("| C28 | Lusso et al. 2019 (arXiv:1907.07692v4) Sect. 3.2")]
assert len(idx) == 1
lines[idx[0]] = "| C28 | — | — | → **F11** |"
open(f"{root}/FINDINGS.md", "w", encoding="utf-8").write("\n".join(lines))
sub1("FINDINGS.md", "**Title** (was C15, C16): Demianski", "**Title** (was C15, C16, C28): Demianski")
with open(f"{root}/LEDGER.md", "a", encoding="utf-8") as f:
    f.write("- 2026-11-15, run 2026-11-15T0428Z — FINDINGS.md `F11`: candidate ids of its title note updated; candidates table row pointer.\n")
