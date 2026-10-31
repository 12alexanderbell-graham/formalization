import sys, pathlib
root = pathlib.Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")

# STATE.md: the F5 result is flat only (dQFlat, Omega0 = 1); the record now says it covers every curvature.
sub("STATE.md",
    "`Checked.Cosmography.CVdQ.dQ_y_third_order` (flat d_Q(y) to y³)",
    "`Checked.Cosmography.CVdQ.dQ_y_third_order` (d_Q(y) to y³, every real K, any C³ a)")
sub("STATE.md",
    " but no separate curved refutation of the printed D² is stated. F5 flat only.",
    " but no separate curved refutation of the printed D² is stated.")
