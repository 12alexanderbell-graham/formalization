#!/usr/bin/env python3
"""Formula-free variants of blind red team X's six defects (written by the judge after reading X's report: NOT blind).
Each restates the defect's false content in words only, on the rewritten phrases of run 2026-11-08T1828Z, so that
rule P1 cannot see it; used to measure what the phrase layer still lets through. Usage: variants_X.py <root> [dNN ...]"""
import sys, pathlib
root = pathlib.Path(sys.argv[1])
P = root / "scripts/trust/phrases.txt"
V = {
 "d01": ("the redshift at observation time {t₀} of light at emission time {t} (scale factor {a})",
         "the redshift at observation time {t} of light at emission time {t₀} (scale factor {a})"),
 "d02": ("the angular-diameter distance, at observation time {t₀}",
         "the angular-diameter distance, the luminosity distance divided once by one plus the redshift, at observation time {t₀}"),
 "d03": ("the molar volume {v} is a critical point of the isotherm {p} (pressure as a function of molar volume at fixed temperature): its first and second derivatives vanish at {v}",
         "the molar volume {v} is a critical point of the isotherm {p} (pressure as a function of molar volume at fixed temperature), which is twice differentiable there with a horizontal inflection point: its first and second derivatives vanish at {v}"),
 "d04": ("with a positive Hubble rate at {t₀} and a positive, differentiable scale factor on that neighbourhood (the law itself is the formula printed with the definition)",
         "with a differentiable scale factor on that neighbourhood (the law itself is the formula printed with the definition)"),
 "d05": ("B and C turn into A and C with rate constant {k₂}, and two B turn into B and C with rate constant {k₃}",
         "B and C turn into A and C with rate constant {k₃}, and two B turn into B and C with rate constant {k₂}"),
 "d06": ("(units in which the speed of light is one; it is minus Ω_k)",
         "(units in which the speed of light is one; it is Ω_k, the curvature density parameter)"),
}
t = P.read_text(encoding="utf-8")
for k in (sys.argv[2:] or sorted(V)):
    old, new = V[k]
    assert t.count(old) >= 1, (k, t.count(old))
    t = t.replace(old, new, 1)  # d04: the first occurrence is IsFlatLCDM's (IsFlatCPL shares the clause)
P.write_text(t, encoding="utf-8")
with open(root / "LEDGER.md", "a", encoding="utf-8") as f:
    f.write("- judge variants of red team X (not blind): phrases of `redshift`, `angDist`, `IsCriticalIsotherm`, `IsFlatLCDM`, `IsRobSolution`, `curvK` reworded.\n")
