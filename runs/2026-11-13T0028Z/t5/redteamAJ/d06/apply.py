import sys, pathlib
root = sys.argv[1]
p = pathlib.Path(root) / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
a = "η₂₀ ≃ 0.15[src]ε, −0.12[src]ε and"
b = "η₂₀ ≃ −0.12[src]ε, 0.15[src]ε and"
assert t.count(a) == 1
p.write_text(t.replace(a, b), encoding="utf-8")
