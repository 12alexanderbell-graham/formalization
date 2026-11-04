import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

sub("Checked/Chemistry/CubicEOS.lean",
    "/-- The critical cubic in `x = v_c/b`. -/",
    "/-- The critical cubic in `x = v_c/b`: its roots `x > 1` give the admissible critical molar volumes. "
    "For every `u` and `w` it has exactly one root `x > 1` (Descartes' rule of signs), so the family needs no "
    "restriction on `u`, `w`. -/")
