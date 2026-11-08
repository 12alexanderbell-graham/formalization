"""Concatenate the scratch lemma files and the candidate headlines into lean/BoundedAll.lean."""
import pathlib, re
d = pathlib.Path(__file__).resolve().parent.parent / "lean"
def body(name):
    t = (d / name).read_text(encoding="utf-8")
    assert t.startswith("import Mathlib\n")
    return t[len("import Mathlib\n"):]
out = ("import Mathlib\nimport Work.FalknerSkan.MonotoneWindow\nimport Work.FalknerSkan.MonotoneExists\n"
       + body("BoundedPos.lean") + body("BoundedUnique.lean")
       + (d / "Headlines.part").read_text(encoding="utf-8"))
(d / "BoundedAll.lean").write_text(out, encoding="utf-8")
print("wrote", d / "BoundedAll.lean")
