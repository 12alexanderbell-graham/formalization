import sys, pathlib
root = sys.argv[1]
p = pathlib.Path(root) / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
a = "Lean covers the flat instance only; the curved statement is sympy + Milne + open-dust Mattig checks (referee)."
b = "Lean covers every curvature, flat and curved (the sign of D²_{L,y} is machine-checked for all K)."
assert t.count(a) == 1
p.write_text(t.replace(a, b), encoding="utf-8")
