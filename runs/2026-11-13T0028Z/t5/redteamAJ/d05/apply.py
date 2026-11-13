import sys, pathlib
root = sys.argv[1]
p = pathlib.Path(root) / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
a = "uniqueness of the reverse-flow branch is not proved and not needed (the refutation covers every solution of the initial-value problem)."
b = "the reverse-flow branch is unique (proved), so the printed value is the wall shear of the only candidate reverse-flow solution and the refutation covers it."
assert t.count(a) == 1
p.write_text(t.replace(a, b), encoding="utf-8")
