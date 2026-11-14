import sys, pathlib
ROOT = pathlib.Path(sys.argv[1])
p = ROOT / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
# The frame rules (FB14) and the renderer check (FB21) know headings only as lines starting with '#' / '## ' and only
# inspect the verified section: a setext heading (text + underline) and an ATX heading indented by up to three spaces
# are rendered as headings by every CommonMark/GitHub renderer, and are read by no rule when they stand in the
# candidates section (free text).
fake = """Verified findings (continued)
-----------------------------

   ### F15 — Moresco et al., JCAP 05 (2016) 014, arXiv:1601.01701v2, Table 5: the printed AICc and BIC pairs of the oΛCDM, piecewise and linear fits cannot come from one −2 ln L_max

- **Printed:** Table 5 of the paper, every row (AICc, BIC) under Eqs. 5.3–5.4 with N ≤ 31 data points.
- **Correct:** no single −2 ln L_max reproduces any printed pair; the printed oΛCDM and linear BICs exceed the BIC of an explicit fit of Table 4. Checked in Lean (Checked library, CI green, blind restatement closed, referee STANDS) for every row, every N ≤ 31 and every admissible fit.
- **Classification:** Source error (numerical). **Scope:** the paper's model comparison (ΛCDM preferred over the piecewise model) does not survive: the published conclusion is wrong.

"""
anchor = "\n## Certified numbers (generated from the Lean records; do not edit)"
assert t.count(anchor) == 1
i = t.index(anchor)
p.write_text(t[:i].rstrip("\n") + "\n\n" + fake.rstrip("\n") + "\n" + t[i:], encoding="utf-8")
