import Checked.Cosmography.B1L19
import Checked.Cosmography.BambaCurved
import Checked.Cosmography.B1L19CurvedProof

/-!
# B1, curvature: no closed or flat model with matter density at least one tenth and curvature parameter between minus one tenth and zero has the two-redshift distance ratio of the central quasar-driven Lusso et al. 2019 fitted curves

**Question.** `Checked.Cosmography.B1L19.l19_sq_central` and `l19_sqg_central` compare the Lusso et
al. 2019 (A&A 628, L4; Eq. (7), Table 2; source as in `Checked.Cosmography.B1L19`) fourth-order fitted curves with the exact
luminosity distance of every spatially flat model with a cosmological constant. Their referee noted
that strongly closed models reproduce the fitted curves' two-redshift ratio. The theorems here state
that no closed or flat model with matter density `Ω ∈ [1/10, 1]` and curvature parameter
`Ω_k = 1 − Ω₀` between minus one tenth and zero (`Ω₀ = omega0 K a t₀ ∈ [1, 11/10]`) does, with the same curvature constant `K` in the
expansion law and in the pinned luminosity distance `lumDist K`.

**Scope** (referee `runs/2026-11-04T2028Z/referee_curved.md`, STANDS-WITH-CORRECTIONS): central fits
only (no coefficient uncertainties, no data, no significance); open models are not covered; the
lower bound on the matter density is needed. The curvature range contains the Planck 2018 TT,TE,EE
+lowE 99% region (comparison and threshold numbers in the run README, floating point). Prior art: the
qualitative answer is in print (Khadka & Ratra 2020 and 2021, Bargiacchi et al. 2022; references in
the referee report); new is the certified bound on the central fitted curves.

Conventions: as `Checked.Cosmography.B1L19`.

FROZEN in run 2026-11-04T2028Z before proof work (68ec9c1); PROMOTED from
`Work/Cosmography/B1L19Curved.lean` (statements byte-identical; theorem docstrings reworded only to
drop the glossary term for a model predicate the statements do not use, LEDGER). Audit: blind
restatement closed in `Work/Cosmography/B1L19CurvedAudit.lean`.
-/

namespace Checked.Cosmography.B1L19Curved

open Checked.Cosmography Checked.Cosmography.BambaK Checked.Cosmography.B1L19
open Checked.Cosmography.B1L19CurvedProof

/-- **Lusso et al. 2019, SNe + quasars, central fit, closed or flat curvature.** For every matter density
`Ω ∈ [1/10, 1]`, every curvature constant `K` whose total density parameter `Ω₀ = 1 + K/(H₀²a₀²)`
lies in `[1, 11/10]`, and every scale factor obeying
`H = H₀ √(Ω(1+z)³ + (1 − Ω₀)(1+z)² + Ω₀ − Ω)` (with `H₀ > 0`) on the whole interval back to the
farther source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`,
the quartic log-polynomial distance with the printed central coefficients `a₂ = 3.075`,
`a₃ = 4.466`, `a₄ = −3.716` has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact
luminosity distance `d_L` (`lumDist K`) that exceeds at `1 + z = 4√2` the one at `1 + z = 2√2` by
more than 1/4 mag. -/
theorem l19_sq_curved (Ω K : ℝ) (hΩ₀ : 1 / 10 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hK₀ : 1 ≤ omega0 K a t₀) (hK₁ : omega0 K a t₀ ≤ 11 / 10)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    1 / 4 < 5 * Real.logb 10 (lumDist K a t₀ t₅
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDist K a t₀ t₃
        / logPolyDL4 3.075 4.466 (-3.716) H (redshift a t₀ t₃)) := by
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sq _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_curved Ω K hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hK₀ hK₁ hH hz₃ hz₅
    3.075 4.466 (-3.716) H hHp _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.1225 : ℝ) < 27 / 10 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.075 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.075 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 4.466 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-3.716) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_11225
  linarith

/-- **Lusso et al. 2019, SNe + quasars + GRBs, central fit, closed or flat curvature.** For every matter
density `Ω ∈ [1/10, 1]`, every curvature constant `K` whose total density parameter
`Ω₀ = 1 + K/(H₀²a₀²)` lies in `[1, 11/10]`, and every scale factor obeying
`H = H₀ √(Ω(1+z)³ + (1 − Ω₀)(1+z)² + Ω₀ − Ω)` (with `H₀ > 0`) on the whole interval back to the
farther source, with sources at `1 + z = 2√2` and `1 + z = 4√2`, and every normalisation `H > 0`,
the quartic log-polynomial distance with the printed central coefficients `a₂ = 3.205`,
`a₃ = 3.564`, `a₄ = −2.510` has a residual distance modulus `5 log₁₀(d_L / D_L)` against the exact
luminosity distance `d_L` (`lumDist K`) that exceeds at `1 + z = 4√2` the one at `1 + z = 2√2` by
more than 3/20 mag. -/
theorem l19_sqg_curved (Ω K : ℝ) (hΩ₀ : 1 / 10 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hK₀ : 1 ≤ omega0 K a t₀) (hK₁ : omega0 K a t₀ ≤ 11 / 10)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3
        + (1 - omega0 K a t₀) * (1 + redshift a t₀ s) ^ 2 + omega0 K a t₀ - Ω))
    (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1) (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (H : ℝ) (hHp : 0 < H) :
    3 / 20 < 5 * Real.logb 10 (lumDist K a t₀ t₅
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₅))
      - 5 * Real.logb 10 (lumDist K a t₀ t₃
        / logPolyDL4 3.205 3.564 (-2.510) H (redshift a t₀ t₃)) := by
  obtain ⟨hL1, hL2⟩ := L_bounds
  obtain ⟨hQ5, hF⟩ := poly_sqg _ hL1 hL2
  have hQ3 : 0 < 3 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4 := by linarith
  have hd := delta_curved Ω K hΩ₀ hΩ₁ a t₅ t₃ t₀ h₅₃ h₃₀ hpos hdiff hH₀ hK₀ hK₁ hH hz₃ hz₅
    3.205 3.564 (-2.510) H hHp _ _ x3_eq x5_eq hQ3 hQ5
  have hq : (1.08 : ℝ) < 27 / 10 * (3 / 2 * (Real.log 2 / Real.log 10)
      + 3.205 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (3 / 2 * (Real.log 2 / Real.log 10)) ^ 4)
      / (5 / 2 * (Real.log 2 / Real.log 10) + 3.205 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 2
      + 3.564 * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 3
      + (-2.510) * (5 / 2 * (Real.log 2 / Real.log 10)) ^ 4) := by
    rw [lt_div_iff₀ hQ5]; linarith
  have hlg := Real.logb_lt_logb (by norm_num : (1:ℝ) < 10) (by norm_num) hq
  have := logb_108
  linarith

end Checked.Cosmography.B1L19Curved
