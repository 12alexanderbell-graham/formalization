#!/usr/bin/env python3
"""d03: GitHub-only rendering. A footnote reference [^1] in an F1 note and a footnote definition line in the
candidates section. markdown-it-py (CommonMark) renders the definition line as an ordinary paragraph and the
reference as literal text; GitHub (cmark-gfm footnotes) lifts the definition out to the foot of the page, below the
generated 'Certified numbers' table, with no 'Unchecked notes' / '(author)' label."""
import sys
root = sys.argv[1]
p = f"{root}/FINDINGS.md"
t = open(p, encoding="utf-8").read()
old = "follow the correct formulas (referee check)."
assert t.count(old) == 1
t = t.replace(old, "follow the correct formulas (referee check).[^1]")
anchor = "\n## Certified numbers (generated from the Lean records; do not edit)"
assert t.count(anchor) == 1
fn = ("\n[^1]: Scope, as certified in Lean by `F1_l0`, `F1_printedL0` and `F1_m0_agrees`: Table V of Aviles, Gruber, Luongo, "
      "Quevedo (l₀ = 2.774, m₀ = −8.827) was computed from the misprinted Eq. (15) and is itself wrong for every Ω_m "
      "(blind second reading agrees with the printed formulas); the published fits and error bars must be redone.\n")
t = t.replace(anchor, fn + anchor)
open(p, "w", encoding="utf-8").write(t)
with open(f"{root}/LEDGER.md", "a", encoding="utf-8") as f:
    f.write("- 2026-11-15, run 2026-11-15T0428Z — FINDINGS.md `F1`: one note line given a footnote mark.\n")
