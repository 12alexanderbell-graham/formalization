import sys, pathlib
root = pathlib.Path(sys.argv[1])


def sub(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old[:50], s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")


sub("FINDINGS.md",
    "## Candidates under verification (UNVERIFIED, not findings)",
    """## Verified findings (addendum, run 0228Z)

### F1 addendum (numerical size of the m₀ misprint)
- **Numbers:** flat ΛCDM, Ω_m = 0.3: the printed m₀ = 1 − (27/2)Ω_m² − 81Ω_m² − (81/2)Ω_m³ gives −8.599, the correct m₀ = 1 − (27/2)Ω_m − 81Ω_m² − (81/4)Ω_m³ gives −8.827; they differ by 2.6 %, so the m₀ misprint is numerically minor at realistic matter densities (the l₀ misprint is the substantive one).
- **Lean evidence (Checked):** `Checked.Cosmography.Aviles.flatLCDM_coeffs` (correct m₀ for every Ω_m).
- **Referee (subagent, independent):** STANDS.

## Candidates under verification (UNVERIFIED, not findings)""")
