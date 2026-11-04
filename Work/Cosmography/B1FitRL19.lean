import Work.Cosmography.B1Fit

/-!
# C27 at fit level: no cubic in the RL19 reading box matches any flat ΛCDM over the quasar range

Risaliti & Lusso 2019 (arXiv:1811.02590v1, the only version) Fig. 3: the filled contours (quasars +
JLA supernovae, cubic log-polynomial fit) are centred at `(a₂, a₃) ≈ (3.46 ± 0.03, 1.63 ± 0.06)`
(two readings: run 0428Z `(3.45, 1.6)`, `runs/2026-10-31T0428Z/rl19_numbers.md`; blind second
reading run 2026-11-04T0228Z from an independent render, pixel centroids, `(3.458, 1.629)`).
The box below, `a₂ ∈ [3.43, 3.49]`, `a₃ ∈ [1.57, 1.69]`, contains both readings with their stated
uncertainty.

**Statement.** For every `Ω ∈ [0, 1]` and every scale factor obeying `H = H₀√(Ω(1+z)³ + 1 − Ω)` back
to the farthest of the sources at `1 + z = √2, 2√2, 4√2`, no cubic log-polynomial with `(a₂, a₃)` in
the box (any normalisation `H > 0`, positive at the three redshifts) has a distance modulus within
0.05 mag of the exact one, up to a common offset, at all three redshifts. With
`Work.Cosmography.B1Fit.fit_direction` this is the certified form of C27: the RL19 centre lies on
the opposite side of the line through the ΛCDM-implied point from every cubic that matches exact
ΛCDM over the quasar range, so the truncation of the cubic does not account for it.
It is a statement about the centre of the published contours, not about the data or their
covariance (not printed).

FROZEN (annex 40.1) in run 2026-11-04T0228Z before proof work.
-/

namespace Work.Cosmography.B1FitRL19

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- **C27 (fit level).** For every `Ω ∈ [0, 1]`, no cubic log-polynomial with `a₂ ∈ [3.43, 3.49]`,
`a₃ ∈ [1.57, 1.69]` (the RL19 Fig. 3 contour centre with its reading uncertainty), normalisation
`H > 0`, positive at `1 + z = √2, 2√2, 4√2`, agrees with the exact distance modulus of a model
obeying `H = H₀√(Ω(1+z)³ + 1 − Ω)` within 0.05 mag up to a common offset at all three redshifts. -/
theorem rl19_box_unmatched (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₅ t₃ t₁ t₀ : ℝ) (h₅₃ : t₅ ≤ t₃) (h₃₁ : t₃ ≤ t₁) (h₁₀ : t₁ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₅ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₅ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₅ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₁ : redshift a t₀ t₁ = √2 - 1) (hz₃ : redshift a t₀ t₃ = 2 * √2 - 1)
    (hz₅ : redshift a t₀ t₅ = 4 * √2 - 1)
    (a₂ a₃ H c : ℝ) (ha₂ : 343 / 100 ≤ a₂ ∧ a₂ ≤ 349 / 100)
    (ha₃ : 157 / 100 ≤ a₃ ∧ a₃ ≤ 169 / 100) (hHp : 0 < H)
    (hp₁ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₁))
    (hp₃ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₃))
    (hp₅ : 0 < logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) :
    ¬ (|5 * Real.logb 10 (lumDistFlat a t₀ t₁ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₁)) - c|
          ≤ 1 / 20 ∧
        |5 * Real.logb 10 (lumDistFlat a t₀ t₃ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₃)) - c|
          ≤ 1 / 20 ∧
        |5 * Real.logb 10 (lumDistFlat a t₀ t₅ / logPolyDL3 a₂ a₃ H (redshift a t₀ t₅)) - c|
          ≤ 1 / 20) := by
  sorry

end Work.Cosmography.B1FitRL19
