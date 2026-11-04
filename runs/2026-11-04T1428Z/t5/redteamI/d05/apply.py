import sys, os
root = sys.argv[1]
def rd(p):
    return open(os.path.join(root, p), encoding="utf-8").read()
def wr(p, s):
    open(os.path.join(root, p), "w", encoding="utf-8").write(s)
def rep(p, old, new):
    s = rd(p); assert s.count(old) == 1, (p, old[:40], s.count(old)); wr(p, s.replace(old, new))
def app(p, add):
    s = rd(p); wr(p, s + add)

LEAN = 'import Checked.Cosmography.B1L19\n\nnamespace Checked.Cosmography.B1L19\n\nopen Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1\n\n/-- **Lusso et al. 2019, SNe + quasars, whole quasar Hubble diagram.** The quartic log-polynomial\ndistance with the printed central coefficients `a₂ = 3.075`, `a₃ = 4.466`, `a₄ = −3.716` rises by\nmore than 7/20 mag less, in distance modulus, than the exact luminosity distance `d_L`\n(`lumDistFlat`) of a flat model with `Ω ∈ [0, 1]`, throughout the quasar redshift range, wherever\nthe two sources sit and for any normalisation `H > 0`; no magnitude offset removes the difference. -/\ntheorem l19_sq_quasar_range (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)\n    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)\n    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)\n    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)\n    (hH₀ : 0 < hubble a t₀)\n    (hH : ∀ s ∈ Set.Icc t₅ t₀,\n      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))\n    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)\n    (H : ℝ) (hHp : 0 < H) :\n    7 / 20 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅\n        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₅))\n      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃\n        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₃)) :=\n  l19_sq_central Ω hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ H hHp\n\nend Checked.Cosmography.B1L19\n'
wr('Checked/Cosmography/B1L19Range.lean', LEAN)
app("Checked.lean", "import Checked.Cosmography.B1L19Range\n")
app("scripts/trust/headlines.txt", 'Checked.Cosmography.B1L19.l19_sq_quasar_range\n')
rep("Checked/Trust/Witnesses.lean", 'import Checked.Cosmography.B1L19\n', 'import Checked.Cosmography.B1L19\nimport Checked.Cosmography.B1L19Range\n')
rep("Checked/Trust/Witnesses.lean", "\nend Checked.Trust.NV", '\ntheorem l19_sq_quasar_range : nonvacuity% Checked.Cosmography.B1L19.l19_sq_quasar_range := by\n  obtain ⟨Ω, a, t₅, t₃, t₀, H, h0, h1, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, hHp⟩ :=\n    Checked.Cosmography.B1L19.hyps_satisfiable_central\n  exact ⟨Ω, h0, h1, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, H, hHp, trivial⟩\n\nend Checked.Trust.NV')
