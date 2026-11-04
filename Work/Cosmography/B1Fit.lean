import Checked.Cosmography.B1Truncation

/-!
# B1 at fit level: across the quasar redshift range, every cubic log-polynomial that matches exact flat ΛCDM is displaced from the ΛCDM-implied point toward larger a₃ (any Ω_M ∈ [0, 1])

**Question (STATE "B1", next step 2; FINDINGS candidate C27; referee 0828Z §3.4).**
Risaliti & Lusso 2019 (Nat. Astron. 3, 272; arXiv:1811.02590) and Lusso et al. 2019
(A&A 628, L4; arXiv:1907.07692) fit `D_L = ln(10)(c/H₀)(x + a₂x² + a₃x³)`, `x = log₁₀(1+z)`,
and measure their > 4σ tension as the distance of the fitted `(a₂, a₃)` from the point flat ΛCDM
implies (`lusA2 Ω`, `lusA3 Ω`, Lusso et al. 2019 Eq. (8)). Yang et al. 2020 (arXiv:1911.01681)
and Banerjee et al. 2021 (arXiv:2009.04109) argue that the cubic is a poor approximant, so that
"ΛCDM seen through the cubic" is not the Taylor point. The earlier certified results
(`Checked.Cosmography.B1Sep.cubic_separation`, `cubic_direction`) used a two-point criterion at
z = 3 and z = 7 (outside the quasar range) and Ω ∈ [0.2, 0.4]; the referee asked for a statement
about fits over the data range and the whole ΛCDM line Ω ∈ [0, 1].

**Statement.** For every flat ΛCDM model with `Ω ∈ [0, 1]` (Friedmann law on the whole interval
back to the farthest source), take sources at the three redshifts with `1 + z = √2, 2√2, 4√2`
(`z ≈ 0.414, 1.828, 4.657`, spanning the RL19 quasar range `z ≤ 5.1`). Every cubic
log-polynomial — any `a₂, a₃`, normalisation `H > 0`, magnitude offset `c`, positive at the three
redshifts — whose distance modulus agrees with the exact one up to the common offset `c` within
0.05 mag at all three redshifts satisfies
`a₂ − a₂^ΛCDM + 1/2 < (20/3) log₁₀2 · (a₃ − a₃^ΛCDM)`
(slope `(20/3) log₁₀ 2 ≈ 2.007`): it lies strictly beyond a line through the ΛCDM-implied point,
on the side of smaller `a₂` / larger `a₃`, by a definite margin.

Why "fit level": a least-squares fit of the cubic to exact ΛCDM over `z ≤ 4.66` or `z ≤ 5.1`
(uniform in z or in ln(1+z)) leaves residuals within ±0.036 mag of a common offset at these three
redshifts for every Ω tried (floating-point exploration, `runs/2026-11-04T0228Z/scripts/lsfit.py`),
so such fits satisfy the hypothesis; the Taylor point itself does not (its residual half-range at
the three points is 0.11–0.23 mag). The hypothesis is weaker than agreement on the whole range,
so the theorem also covers every minimax fit within 0.05 mag over any range containing the
three redshifts. It is not a statement about fits to data with errors.

Positivity of the polynomial distance at the three redshifts is assumed (a negative distance has
no distance modulus; `Real.logb` would silently take the absolute value).

Conventions: as `Checked.Cosmography.B1` (`c = 1`, `hubble a t = ȧ/a`,
`redshift a t₀ t = a(t₀)/a(t) − 1`, `lumDistFlat`; distance-modulus difference `5 log₁₀(d/d')`).

FROZEN (annex 40.1) in run 2026-11-04T0228Z before proof work.
-/

namespace Work.Cosmography.B1Fit

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- **B1 at fit level (direction).** In every flat ΛCDM model with `Ω ∈ [0, 1]`, with sources at
`1 + z = √2, 2√2, 4√2` (`z ≈ 0.41, 1.83, 4.66`), every cubic log-polynomial (coefficients
`a₂, a₃`, normalisation `H > 0`, positive at the three redshifts) whose distance modulus agrees
with the exact one up to a common offset `c` within 0.05 mag at all three redshifts satisfies
`a₂ − lusA2 Ω + 1/2 < (20/3) log₁₀ 2 · (a₃ − lusA3 Ω)`: it lies beyond a line through the
ΛCDM-implied point, towards smaller `a₂` and larger `a₃`, by a margin of 1/2 in `a₂`. -/
theorem fit_direction (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₁ : t₃ ≤ t₁) (h₁₀ : t₁ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅))
    (hm₁ : |5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
      ≤ 1 / 20)
    (hm₃ : |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
      ≤ 1 / 20)
    (hm₅ : |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
      ≤ 1 / 20) :
    a₂ - lusA2 Ω + 1 / 2 < 20 / 3 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  sorry

end Work.Cosmography.B1Fit
