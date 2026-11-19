#!/usr/bin/env python3
"""Reader pages for test EF (run 2026-11-19T2028Z): arms N (no source, verbatim from test LN), EP (a model eponym of the
headline used as the thing the statement differs from), F (a non-document word, 'the formula', used the same way).

Usage: make_pages_EF.py <commit> <outdir>
Writes <outdir>/<reader>/STATE.md and CLAIMS.md for readers r48..r56 from STATE.md and CLAIMS_READER.md at <commit>.
Each arm line is inserted as one bullet directly under its STATE.md section heading (matched by heading prefix).
Adapted from runs/2026-11-19T0828Z/t5/make_pages.py (same insertion, same reader prompt).
"""
import subprocess, sys, pathlib

HEADS = {
    "many": "## Mathematics: multiplicity of radial solutions of the Gelfand problem in the 3-D ball",
    "extrema": "## Mathematics: every turning point of the radial Gelfand branch in the 3-D ball",
    "fs3": "## Fluid mechanics: reversed-flow row β = −0.03 of Ganapol 2010 Table 7 (",
}
N = {  # verbatim from runs/2026-11-19T0228Z/t5/reader_brief_N.md
    "many": "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers.",
    "extrema": "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent.",
    "fs3": "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse one.",
}
EP = {  # run 2026-11-19T2028Z: the N lines with a model eponym of the headline as the reference (M8 limit (1))
    "many": "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers to Gelfand.",
    "extrema": "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent to Gelfand.",
    "fs3": "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse of Falkner–Skan.",
}
F = {  # run 2026-11-19T2028Z: the N lines with a non-document word as the reference (M8 limit (2))
    "many": "- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers of the formula.",
    "extrema": "- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent of the formula.",
    "fs3": "- `fs_neg_reversed_wall_shear_3_exists`: the sign of the pressure gradient term in the equation is the inverse of the formula.",
}
ARMS = {"N": N, "EP": EP, "F": F}
# Reader -> arm, interleaved so no arm is launched as a block.
READERS = {"r48": "EP", "r49": "N", "r50": "F", "r51": "F", "r52": "EP", "r53": "N", "r54": "N", "r55": "F", "r56": "EP"}


def show(commit, path):
    return subprocess.run(["git", "show", f"{commit}:{path}"], check=True, capture_output=True, text=True).stdout


# Lines of STATE.md that describe earlier reader tests of this shape are dropped from every arm alike
# (PROMPT note of run 2026-11-18T0828Z: never let the material describe the test).
DROP = ("- **M6 of `scripts/trust/check_headline_mentions.py`", "- **Status headings kept in step with the judge;",
        "- **Lines naming a source, measured;", "- **M8 of `scripts/trust/check_headline_mentions.py`")


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
