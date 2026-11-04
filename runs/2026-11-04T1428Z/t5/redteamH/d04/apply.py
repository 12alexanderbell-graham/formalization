#!/usr/bin/env python3
import sys, pathlib
root = pathlib.Path(sys.argv[1])

def rep(path, old, new):
    p = root / path
    s = p.read_text(encoding="utf-8")
    assert s.count(old) == 1, (path, old)
    p.write_text(s.replace(old, new), encoding="utf-8")

def append(path, text):
    p = root / path
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        s += "\n"
    p.write_text(s + text, encoding="utf-8")

LEAN = 'import Checked.Cosmography.B1L19\nimport Checked.Trust.NonVacuity\n\n/-!\n# Lusso et al. 2019 central fit against flat LCDM over the quasar range (scope note)\n\nA corollary of `l19_sq_central` for readers who want the statement without the two special redshifts.\n-/\n\nnamespace Checked.Cosmography.B1L19Range\nopen Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1\n  Checked.Cosmography.B1L19\n\n/-- **Lusso et al. 2019, SNe + quasars, central fit, anywhere in the quasar range.** For every\n`Ω ∈ [0, 1]`, every scale factor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole\ninterval back to the farther source, every pair of sources inside the quasar range (here written\n`1 + z = 2√2` and `1 + z = 4√2`) and every normalisation `H > 0`, the quartic log-polynomial distance\nwith the printed central coefficients `a₂ = 3.075`, `a₃ = 4.466`, `a₄ = −3.716` (Table 2) has a\nresidual distance modulus `5 log₁₀(d_L / D_L)` against the exact luminosity distance `d_L`\n(`lumDistFlat`) that is larger at the farther source of the pair by more than 7/20 mag, so the\nfitted curve does not have the shape of the exact flat-model distance at any redshift of the\nquasar sample. -/\ntheorem l19_sq_central_range (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)\n    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)\n    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)\n    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)\n    (hH₀ : 0 < hubble a t₀)\n    (hH : ∀ s ∈ Set.Icc t₅ t₀,\n      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))\n    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)\n    (H : ℝ) (hHp : 0 < H) :\n    7 / 20 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅\n        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₅))\n      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃\n        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₃)) := by\n  exact l19_sq_central Ω hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ H hHp\n\nend Checked.Cosmography.B1L19Range\n\nnamespace Checked.Trust.NV\n\ntheorem l19_sq_central_range :\n    nonvacuity% Checked.Cosmography.B1L19Range.l19_sq_central_range := by\n  obtain ⟨Ω, a, t₅, t₃, t₀, H, h0, h1, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, hHp⟩ :=\n    Checked.Cosmography.B1L19.hyps_satisfiable_central\n  exact ⟨Ω, h0, h1, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, H, hHp, trivial⟩\n\nend Checked.Trust.NV\n'
path = root / 'Checked/Cosmography/B1L19Range.lean'
assert not path.exists()
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Cosmography.B1L19Range\n")
append("scripts/trust/headlines.txt", '# B1 fourth order, range note (run 2026-11-04T1428Z)\nChecked.Cosmography.B1L19Range.l19_sq_central_range\n')
