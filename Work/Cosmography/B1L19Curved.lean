import Checked.Cosmography.B1L19
import Checked.Cosmography.BambaCurved

/-!
# B1, curvature: no closed or flat ΛCDM model with `Ω_k ≥ −1/10` and `Ω_m ∈ [1/10, 1]` has the shape of the quasar-driven Lusso et al. 2019 fitted curves between `1 + z = 2√2` and `4√2`

**Question (STATE "Exact next step" 2; referee of run 2026-11-04T1228Z, §4.3(iii)).** The flat
result `Checked.Cosmography.B1L19.l19_sq_central` / `l19_sqg_central` compares the Lusso et al. 2019
(A&A 628, L4; arXiv:1907.07692v4, Eq. (7), Table 2) fourth-order fitted curves with the exact
luminosity distance of every *flat* ΛCDM model. The referee noted that strongly closed ΛCDM models
reproduce the fitted curves' two-redshift ratio. Question: how closed must a ΛCDM model be to do so?
This file states that no model with spatial curvature parameter `Ω_k = 1 − Ω₀ ∈ [−1/10, 0]`
(closed or flat; `Ω₀ = omega0 K a t₀ = 1 + K/(H₀² a₀²)`, the total density parameter) and matter
density `Ω ∈ [1/10, 1]` does: the residual distance modulus `5 log₁₀(d_L/D_L)` rises between
`1 + z = 2√2` and `1 + z = 4√2` by more than 1/4 mag (SNe + quasars, `a₂ = 3.075`, `a₃ = 4.466`,
`a₄ = −3.716`) and by more than 3/20 mag (SNe + quasars + GRBs, `3.205`, `3.564`, `−2.510`),
whatever the normalisation of the fit. The range `|Ω_k| ≤ 1/10` contains every curvature allowed by
the CMB alone (Planck 2018 TT,TE,EE+lowE: `Ω_k = −0.044 (+0.018/−0.015)`), so closing the universe
within that range cannot turn the fitted shape into a ΛCDM shape.

The model: `H(z) = H₀ √(Ω(1+z)³ + Ω_k(1+z)² + Ω₀ − Ω)` with `Ω_k = 1 − Ω₀` on the whole interval
back to the farther source (cosmological constant `Ω_Λ = Ω₀ − Ω ≥ 0`); `d_L` is the pinned
`BambaK.lumDist K` with the same curvature constant `K` (`a₀ (1+z) S_K(χ)`), so the curvature in the
expansion law and in the distance is one and the same.

Floating point (`runs/2026-11-04T2028Z/scripts/curved.py`): the exact ratio
`d_L(4√2 − 1)/d_L(2√2 − 1)` over the domain is at least 2.8227 (at `Ω = 1`, `Ω_k = −1/10`); the
central quartics give 2.4009 and 2.4697; with `Ω ≥ 1/10`, ratios that low need `Ω_k` below about
−0.26 (at `Ω = 1/10`, near the bounce boundary; `runs/2026-11-04T2028Z/scripts/threshold.py`).
These numbers are not claims of the theorems.

Conventions: as `Checked.Cosmography.B1L19` (`c = 1`, `hubble a t = ȧ/a`,
`redshift a t₀ t = a(t₀)/a(t) − 1`, `logPolyDL4`, distance-modulus difference `5 log₁₀(d/d')`).

FROZEN (annex 40.1) in run 2026-11-04T2028Z before proof work.
-/

namespace Work.Cosmography.B1L19Curved

open Checked.Cosmography Checked.Cosmography.BambaK Checked.Cosmography.B1L19

/-- **Lusso et al. 2019, SNe + quasars, central fit, closed or flat ΛCDM.** For every matter density
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
  sorry

/-- **Lusso et al. 2019, SNe + quasars + GRBs, central fit, closed or flat ΛCDM.** For every matter
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
  sorry

end Work.Cosmography.B1L19Curved
