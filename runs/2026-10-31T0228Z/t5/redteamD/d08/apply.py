import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


sub("FINDINGS.md",
    "`cvdQClaim_false`, `cvdQClaimPast_false` (flat de Sitter).",
    "`cvdQClaim_false`, `cvdQClaimPast_false` (flat de Sitter). Curved case: `Checked.Cosmography.CVdQ.dQ_curved_third_order` (every real K and Ω₀: H₀d_Q = y[1 − (q₀/2)y + Q²y²] + o(y³) with Q² = (1/24)[3 − 2q₀ + 12q₀² − 4(j₀ + Ω₀)]) and `printedQ2_fails_curved` (printed Q² false for every K with the curved analogue of the flat condition).")
sub("STATE.md",
    " F5 flat only.",
    " F5: the curved case is covered by `Checked.Cosmography.CVdQ.dQ_curved_third_order`.")
