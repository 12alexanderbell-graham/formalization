#!/usr/bin/env python3
"""Reader pages for the three-reader test of run 2026-11-18T0228Z (pre-registered in t5/reader_brief.md).

usage: make_reader_pages.py <repo root> <out dir>
Writes, from the repo's CLAIMS.md and STATE.md:
  claims_clean.md      = CLAIMS.md
  claims_defect.md     = CLAIMS.md + W (a withdrawal sentence at the end of the paraphrase of
                         gelfand_pde_radial_many_centre; nothing generated contradicts it)
                         + G (the paraphrase of fs_neg_reversed_wall_shear_3_exists claims the
                         result for a range of beta; the generated claim fixes beta = -3/100)
  claims_generated.md  = CLAIMS.md with every author paraphrase block removed (candidate fix)
  state_defect.md      = STATE.md + W' (a withdrawal bullet in the Gelfand multiplicity section)
"""
import re, sys
from pathlib import Path

root, out = Path(sys.argv[1]), Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
claims = (root / "CLAIMS.md").read_text()
state = (root / "STATE.md").read_text()

def section(text, name):
    i = text.index(f"## `{name}`\n")
    j = text.find("\n## ", i + 1)
    return i, (len(text) if j < 0 else j + 1)

# W: withdrawal, nothing generated contradicts it
W = ("> Status: withdrawn after review: a referee found a fidelity flaw in this frozen statement (it does not\n"
     "> say what the source result says), so it must not be cited until it is re-frozen and re-proved.\n")
i, j = section(claims, "gelfand_pde_radial_many_centre")
sec = claims[i:j]
assert sec.endswith("centre.\n") or sec.rstrip().endswith("centre."), sec[-200:]
sec_w = sec.rstrip("\n") + "\n" + W + "\n"
d = claims[:i] + sec_w + claims[j:]

# G: overgeneralisation, contradicted by the generated claim (beta fixed to -3/100)
i, j = section(d, "fs_neg_reversed_wall_shear_3_exists")
sec = d[i:j]
old = "> Falkner–Skan with β = −3/100: there is a solution"
assert old in sec
new = ("> Falkner–Skan in the reversed-flow regime, β-independent on the whole range −3/100 ≤ β < 0: there is a solution")
d = d[:i] + sec.replace(old, new) + d[j:]
(out / "claims_clean.md").write_text(claims)
(out / "claims_defect.md").write_text(d)

# candidate fix: drop every paraphrase block (the label line and the quoted lines after it)
g = re.sub(r"Author's paraphrase \(docstring; not generated, checked only by the prose rules\):\n\n(?:>.*\n)+\n?", "", claims)
pre = re.compile(r"The author's docstring follows,\s+labelled as a paraphrase: \*\*where the paraphrase and the generated\s+claim differ, the generated\s+claim is what was proved\.\*\*")
assert pre.search(g), "preamble sentence moved"
g = pre.sub("Author docstrings are not shown on this page.", g)
assert "paraphrase" not in g, "paraphrase left"
(out / "claims_generated.md").write_text(g)

# W' in STATE.md
hdr = "## Mathematics: multiplicity of radial solutions of the Gelfand problem in the 3-D ball"
k = state.index(hdr); e = state.index("\n", k) + 1
Wp = ("- **Withdrawn (2026-11-18, after the CI read):** a referee found a fidelity flaw in the frozen statement "
      "(it does not say what the source result says); `gelfand_pde_radial_many_centre` is no longer PROVED and "
      "must not be cited until it is re-frozen and re-proved.\n")
(out / "state_defect.md").write_text(state[:e] + Wp + state[e:])
print("ok", len(claims), len(d), len(g))
