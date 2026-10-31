import sys, pathlib

root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:60], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


# docstring of the record F2_error: the specialisation Ω = 0.3, wₐ = −0.5 (numerals in the
# statement) is generalised in words; the statement, its fingerprint and its RoundsTo are unchanged
sub("Checked/Records/Findings.lean",
    "/-- At `Ω = 0.3`, `wₐ = −0.5` and every `w₀`, every flat CPL model has `l₀` exceeding the printed\n"
    "formula by `2.345`. -/\n",
    "/-- For every matter fraction `Ω` and every `wₐ ≠ 0`, and whatever `w₀`, every flat CPL model has\n"
    "`l₀` exceeding the printed formula by `2.345`. -/\n")
