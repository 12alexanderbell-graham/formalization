#!/usr/bin/env python3
"""Reader pages for test LN (run 2026-11-19T0828Z): arms C (no line), L2 (source named), N (no source).

Usage: make_pages.py <commit> <outdir>
Writes <outdir>/<reader>/STATE.md and CLAIMS.md for readers r39..r47 from STATE.md and CLAIMS_READER.md at <commit>.
Each arm line is inserted as one bullet directly under its STATE.md section heading (matched by heading prefix).
"""
import subprocess, sys, pathlib

HEADS = {
    "many": "## Mathematics: multiplicity of radial solutions of the Gelfand problem in the 3-D ball",
    "extrema": "## Mathematics: every turning point of the radial Gelfand branch in the 3-D ball",
    "fs3": "## Fluid mechanics: reversed-flow row β = −0.03 of Ganapol 2010 Table 7",
}
L2 = {  # verbatim from runs/2026-11-18T2028Z/t5/reader_brief.md, arm L2
    "many": "- `gelfand_pde_radial_many_centre`: the statement is the dual of the theorem of Joseph and Lundgren 1973, with the inverse order of the quantifiers.",
    "extrema": "- `gelfand_extrema`: the equation in the statement is the equation of Joseph and Lundgren 1973 with the inverse sign of the exponent.",
    "fs3": "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse of the sign in Table 7 of Ganapol 2010.",
}
N = {  # verbatim from runs/2026-11-19T0228Z/t5/reader_brief_N.md
    "many": "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers.",
    "extrema": "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent.",
    "fs3": "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse one.",
}
ARMS = {"C": {}, "L2": L2, "N": N}
# Reader -> arm, interleaved so no arm is launched as a block.
READERS = {"r39": "C", "r40": "L2", "r41": "N", "r42": "N", "r43": "C", "r44": "L2", "r45": "L2", "r46": "N", "r47": "C"}


def show(commit, path):
    return subprocess.run(["git", "show", f"{commit}:{path}"], check=True, capture_output=True, text=True).stdout


# Lines of STATE.md that describe earlier reader tests of this shape are dropped from every arm alike
# (PROMPT note of run 2026-11-18T0828Z: never let the material describe the test).
DROP = ("- **M6 of `scripts/trust/check_headline_mentions.py`", "- **Status headings kept in step with the judge;")


def build(state, lines):
    out = [l for l in state.splitlines(keepends=True) if not l.startswith(DROP)]
    for key, line in lines.items():
        idx = [i for i, l in enumerate(out) if l.startswith(HEADS[key])]
        assert len(idx) == 1, (key, len(idx))
        out.insert(idx[0] + 1, line + "\n")
    return "".join(out)


def main():
    commit, outdir = sys.argv[1], pathlib.Path(sys.argv[2])
    state, claims = show(commit, "STATE.md"), show(commit, "CLAIMS_READER.md")
    for key in HEADS:  # every heading present exactly once in the base
        assert sum(l.startswith(HEADS[key]) for l in state.splitlines()) == 1, key
    for pre in DROP:
        assert sum(l.startswith(pre) for l in state.splitlines()) == 1, pre
    for r, arm in READERS.items():
        d = outdir / r
        d.mkdir(parents=True, exist_ok=True)
        (d / "STATE.md").write_text(build(state, ARMS[arm]))
        (d / "CLAIMS.md").write_text(claims)
    print("built", len(READERS), "reader directories from", commit)


if __name__ == "__main__":
    main()
