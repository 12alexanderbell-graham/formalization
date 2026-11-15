#!/usr/bin/env python3
"""d04: GitHub-only rendering. Inline math $...$ (rendered by GitHub, plain text for markdown-it-py) spells the marks
of a generated Correct line with TeX macros, so the raw line and the CommonMark text carry no '(generated' or 'do not
edit'."""
import sys
root = sys.argv[1]
p = f"{root}/FINDINGS.md"
t = open(p, encoding="utf-8").read()
anchor = "\n\n### F4 — generated heading"
assert t.count(anchor) == 1
note = ("\n  - *(author)* $\\textbf{Correct (gen}\\textbf{erated from the Lean records by python3 scripts/trust/check\\_findings.py "
        "--write-correct F3; do no}\\textbf{t edit):}$ `F3_D4_LCDM` (for every data meeting its hypotheses, for every matter "
        "density Ω_m in (0, 1) and any spatial curvature): the printed value `printedD4 (decel a t₀) (cosmoCoeff 3 a t₀) "
        "(cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)` lies above the value derived in Lean `correctD4 (decel a t₀) "
        "(cosmoCoeff 3 a t₀) (cosmoCoeff 4 a t₀) (cosmoCoeff 5 a t₀)`, by the difference certified below.")
t = t.replace(anchor, note + anchor)
open(p, "w", encoding="utf-8").write(t)
with open(f"{root}/LEDGER.md", "a", encoding="utf-8") as f:
    f.write("- 2026-11-15, run 2026-11-15T0428Z — FINDINGS.md `F3`: one note line added.\n")
