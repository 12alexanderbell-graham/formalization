import sys, pathlib
root = sys.argv[1]
p = pathlib.Path(root) / "FINDINGS.md"
t = p.read_text(encoding="utf-8")
a = "m₀ = 1 − (27/2)Ω_m − 81Ω_m² − (81/4)Ω_m³. Printed q₀"
b = "m₀ = 1 − (27/2)Ω_m − 81Ω_m² − (81/2)Ω_m³. Printed q₀"
assert t.count(a) == 1
p.write_text(t.replace(a, b), encoding="utf-8")
