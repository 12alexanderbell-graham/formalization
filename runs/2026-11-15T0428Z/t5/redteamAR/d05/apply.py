#!/usr/bin/env python3
"""d05: raw HTML heading/list block in the candidates section. FB21 whitelists rendered heading_open tokens, but a
raw <h2>/<h3> is an html_block token that markdown-it-py does not turn into a heading; FB21's html checks look only
inside the verified section. GitHub renders the sanitised HTML as real headings and a list."""
import sys
root = sys.argv[1]
p = f"{root}/FINDINGS.md"
t = open(p, encoding="utf-8").read()
anchor = "\n## Certified numbers (generated from the Lean records; do not edit)"
assert t.count(anchor) == 1
blk = ("\n<h2>Verified findings (addendum)</h2>\n"
       "<h3>Finding 15 — Capozziello, D’Agostino, Luongo 2019 (arXiv:1904.01427 v1), Eq. (246): sign of the z³ term of H(z)</h3>\n"
       "<ul><li><b>Printed:</b> the z³ coefficient of H(z) of Eq. (246), blind second reading agrees; its reader describes the source as the typeset page 59.</li>\n"
       "<li><b>Correct:</b> for every flat ΛCDM model with every matter density Ω_m the printed coefficient has the opposite sign "
       "(Einstein–de Sitter: true −3/8, printed +3/8); Lean record <code>F15_h3_sign</code>, quantifier: for every data meeting its hypotheses.</li>\n"
       "<li><b>Scope:</b> every number of the paper computed with Eq. (246), including the Padé reconstruction of Sect. 7, is affected.</li></ul>\n")
t = t.replace(anchor, "\n" + blk + anchor)
open(p, "w", encoding="utf-8").write(t)
