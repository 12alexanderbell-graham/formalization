import sys, pathlib
root = sys.argv[1]
p = pathlib.Path(root) / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
old = "so the caption is false only in the classical class (exponential approach), the class in which the paper calls the solution unique."
new = "so the caption is false for every zero-wall-shear solution, whatever its approach to the edge velocity (exponential or algebraic), and the printed value is the parameter of no zero-wall-shear solution at all."
assert t.count(old) == 1
p.write_text(t.replace(old, new), encoding="utf-8")
