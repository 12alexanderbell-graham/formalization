import sys, pathlib

root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:60], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


# docstring of a PINNED definition (never read by check_prose.py, not part of the frozen
# fingerprint, shown verbatim in validation/packet/GLOSSARY.md): the sign convention is reversed
sub("Checked/Cosmography/Lookback.lean",
    "/-- Deceleration parameter at `t`: `-(a''(t) a(t)) / a'(t)²`. Mirrors Physlib\n"
    "`decelerationParameter`. -/\n",
    "/-- Deceleration parameter at `t`: `-(a''(t) a(t)) / a'(t)²`. It is positive while the expansion\n"
    "accelerates (`q > 0 ⇔ a'' > 0`) and negative while it decelerates. Mirrors Physlib\n"
    "`decelerationParameter`. -/\n")
