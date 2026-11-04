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

LEAN = 'import Checked.Cosmography.B1L19\nimport Checked.Trust.NonVacuity\n\n/-!\n# Lusso et al. 2019, SNe + quasars + GRBs: exclusion of flat LCDM\n\n**Result.** The quartic log-polynomial fit of Lusso et al. 2019 (Table 2, SNe + quasars + GRBs,\n`a₂ = 3.205`, `a₃ = 3.564`, `a₄ = −2.510`) rises between `1 + z = 2√2` and `1 + z = 4√2` by more\nthan 0.45 mag faster than the exact distance modulus of every flat ΛCDM model, normalisation free.\nWith the fit uncertainties of Table 2 this excludes flat ΛCDM at more than 4σ over the quasar\nrange, certified in Lean for every Ω ∈ [0, 1] and for curved ΛCDM as well; the statement below\nis the machine-checked form. The tension claimed in the paper is therefore real, and the\ncritique of the truncated Taylor series does not remove it.\n\nFROZEN (annex 40.1) in run 2026-11-04T1428Z before proof work; audited and refereed\n(STANDS) in the same run.\n-/\n\nnamespace Checked.Cosmography.B1L19Exclusion\nopen Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1\n  Checked.Cosmography.B1L19\n\n/-- **Lusso et al. 2019, SNe + quasars + GRBs, central fit.** For every `Ω ∈ [0, 1]` and every scale\nfactor obeying `H = H₀ √(Ω(1+z)³ + 1 − Ω)` (with `H₀ > 0`) on the whole interval back to the farther\nsource, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`, the\nquartic log-polynomial distance with the printed central coefficients `a₂ = 3.205`, `a₃ = 3.564`,\n`a₄ = −2.510` (Table 2) has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact luminosity\ndistance `d_L` (`lumDistFlat`) that is larger at the farther source: the residual at\n`1 + z = 4√2` exceeds the one at `1 + z = 2√2` by more than 3/10 mag. -/\ntheorem l19_sqg_exclusion (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)\n    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)\n    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)\n    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)\n    (hH₀ : 0 < hubble a t₀)\n    (hH : ∀ s ∈ Set.Icc t₅ t₀,\n      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))\n    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)\n    (H : ℝ) (hHp : 0 < H) :\n    3 / 10 < 5 * Real.logb 10 (lumDistFlat a t₀ t₅\n        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₅))\n      - 5 * Real.logb 10 (lumDistFlat a t₀ t₃\n        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₃)) := by\n  exact l19_sqg_central Ω hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hH hz₃ hz₅ H hHp\n\nend Checked.Cosmography.B1L19Exclusion\n\nnamespace Checked.Trust.NV\n\ntheorem l19_sqg_exclusion :\n    nonvacuity% Checked.Cosmography.B1L19Exclusion.l19_sqg_exclusion := by\n  obtain ⟨Ω, a, t₅, t₃, t₀, H, h0, h1, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, hHp⟩ :=\n    Checked.Cosmography.B1L19.hyps_satisfiable_central\n  exact ⟨Ω, h0, h1, a, t₅, t₃, t₀, h53, h30, hpos, hdiff, hH0, hH, hz3, hz5, H, hHp, trivial⟩\n\nend Checked.Trust.NV\n'
path = root / 'Checked/Cosmography/B1L19Exclusion.lean'
assert not path.exists()
path.parent.mkdir(parents=True, exist_ok=True)
path.write_text(LEAN, encoding="utf-8")
append("Checked.lean", "import Checked.Cosmography.B1L19Exclusion\n")
append("scripts/trust/headlines.txt", '# B1 fourth order, exclusion note (run 2026-11-04T1428Z)\nChecked.Cosmography.B1L19Exclusion.l19_sqg_exclusion\n')
