import sys, pathlib
root = pathlib.Path(sys.argv[1])
def rep(rel, old, new):
    p = root / rel
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (rel, old, s.count(old))
    p.write_text(s.replace(old, new), encoding="utf-8")
# the printed Eq. (15) l0 claim and its pointwise refutation, changed in lockstep
rep("Checked/Cosmography/LCDMCoefficients.lean",
    "cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2",
    "cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 4 * Ω ^ 2")
rep("Checked/Cosmography/LCDMCoefficients.lean",
    "formula gives `−19/2`, the true value is `35/2`.",
    "formula gives `−11/4`, the true value is `35/2`.")
rep("Checked/Cosmography/LCDMWitness.lean",
    "cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 2 * Ω ^ 2 := by",
    "cosmoCoeff 5 a t₀ = 1 + 3 * Ω - 27 / 4 * Ω ^ 2 := by")
# records kept consistent with the (mis)transcription
rep("FINDINGS.md", "l₀ = 1 + 3Ω_m − (27/2)Ω_m², m₀", "l₀ = 1 + 3Ω_m − (27/4)Ω_m², m₀")
rep("FINDINGS.md", "true l₀ = 35/2 vs printed −19/2", "true l₀ = 35/2 vs printed −11/4")
rep("FINDINGS.md", "the printed l₀ is 0.685 instead of 3.115", "the printed l₀ is 1.2925 instead of 3.115")
