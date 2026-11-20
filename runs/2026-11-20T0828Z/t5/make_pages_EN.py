#!/usr/bin/env python3
"""Reader pages for test EN (run 2026-11-20T0828Z): arm EP's lines with the eponym followed by a model noun ('to the
Gelfand problem'; the shape M10 exempts as a model's name, six M10h lines passed by it) in place of the bare eponym, six readers, beside a control arm C
of three readers with no inserted line. Same builder as make_pages_ND.py (same insertion, same drops, same prompt).

Usage: make_pages_EN.py <commit> <outdir>
Writes <outdir>/<reader>/STATE.md and CLAIMS.md for readers r84..r92 from STATE.md and CLAIMS_READER.md at <commit>.
Each arm line is inserted as one bullet directly under its STATE.md section heading (matched by heading prefix).
"""
import subprocess, sys, pathlib

HEADS = {
    "many": "## Mathematics: multiplicity of radial solutions of the Gelfand problem in the 3-D ball",
    "extrema": "## Mathematics: every turning point of the radial Gelfand branch in the 3-D ball",
    "fs3": "## Fluid mechanics: reversed-flow row β = −0.03 of Ganapol 2010 Table 7 (",
}
EN = {  # arm EP's lines with the eponym followed by a model noun; each passes M1-M11 on main
    "many": ["- `gelfand_pde_radial_many_centre`: the statement has the inverse order of the quantifiers to the Gelfand problem."],
    "extrema": ["- `gelfand_extrema`: the equation in the statement has the inverse sign of the exponent to the Gelfand problem."],
    "fs3": ["- `fs_neg_reversed_wall_shear_3_exists` has the pressure gradient term with the inverse sign to the Falkner Skan problem."],
}
C = {"many": [], "extrema": [], "fs3": []}
ARMS = {"EN": EN, "C": C}
READERS = {"r84": "EN", "r85": "C", "r86": "EN", "r87": "EN", "r88": "C", "r89": "EN", "r90": "EN", "r91": "C", "r92": "EN"}

# Lines of STATE.md that describe earlier reader tests of this shape are dropped from every arm alike
# (PROMPT note of run 2026-11-18T0828Z: never let the material describe the test). EP2's list plus the two lines added by
# run 0228Z (the M10 bullet and its daily-review line).
DROP = ("- **M6 of `scripts/trust/check_headline_mentions.py`", "- **Status headings kept in step with the judge;",
        "- **Lines naming a source, measured;", "- **M8 of `scripts/trust/check_headline_mentions.py`",
        "- **M9 of `scripts/trust/check_headline_mentions.py`", "- Run 2028Z (part 3): a line comparing a statement with",
        "- **M10 of `scripts/trust/check_headline_mentions.py`", "- Run 0228Z (part 3): a line comparing a statement with")


def show(commit, path):
    return subprocess.run(["git", "show", f"{commit}:{path}"], check=True, capture_output=True, text=True).stdout


def build(state, lines):
    out = [l for l in state.splitlines(keepends=True) if not l.startswith(DROP)]
    for key, ls in lines.items():
        idx = [i for i, l in enumerate(out) if l.startswith(HEADS[key])]
        assert len(idx) == 1, (key, len(idx))
        for j, line in enumerate(ls):
            out.insert(idx[0] + 1 + j, line + "\n")
    return "".join(out)


def main():
    commit, outdir = sys.argv[1], pathlib.Path(sys.argv[2])
    state, claims = show(commit, "STATE.md"), show(commit, "CLAIMS_READER.md")
    for key in HEADS:
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
