import sys, pathlib

root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:60], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


# docstring of the refutation printedD2y_fails: polarity reversed (holds / no correction needed).
# The statement is unchanged (`¬ ... =o ...`), so nothing frozen changes.
sub("Checked/Cosmography/BambaDLy.lean",
    "/-- The printed `D²_{L,y}` (Bamba et al. 2012, Eq. (10.54)) fails in every flat model, scale factor `C³`\n"
    "at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0` and `11 − 5q₀ + 3q₀² − j₀ ≠ 0`: the flat `d_L(y)` series with it is\n"
    "not `d_L + o(y³)` as `t → t₀` (two-sided limit; past-only version: `printedD2y_fails_past`). -/\n",
    "/-- The printed `D²_{L,y}` (Bamba et al. 2012, Eq. (10.54)) holds in every flat model, scale factor `C³`\n"
    "at `t₀` with `a(t₀) ≠ 0`, `H₀ ≠ 0` and `11 − 5q₀ + 3q₀² − j₀ ≠ 0`: the flat `d_L(y)` series with it is\n"
    "`d_L + o(y³)` as `t → t₀`, so no correction of its sign is needed (two-sided limit; past-only\n"
    "version: `printedD2y_fails_past`). -/\n")
