import sys
from pathlib import Path
root = Path(sys.argv[1])
def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, s.count(old), old[:60])
    p.write_text(s.replace(old, new), encoding="utf-8")

p = root / "TRUSTED_DEFINITIONS.md"
lines = p.read_text(encoding="utf-8").split("\n")
idx = [i for i, l in enumerate(lines) if l.startswith("| `CPL.IsFlatCPL` |")]
assert len(idx) == 1
row = ("| `CubicEOS.cubicP`, `CubicEOS.critCubic`, `Coexistence.acentric` | blind `CriticalSpec` and `MaxwellSpec` "
       "(van der Waals critical isotherm and exact coexistence anchors; the generalized family with (u, w) = (0, 0), (1, 0), (2, −1) "
       "is covered through the same anchors) | yes, `criticalSpec_pins`, `maxwellSpec_pins` (every a, b, R > 0; Redlich–Kwong and "
       "Peng–Robinson forms checked against their critical constants) |")
lines.insert(idx[0] + 1, row)
p.write_text("\n".join(lines), encoding="utf-8")
