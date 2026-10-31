import Checked.Cosmography.B1Truncation

/-!
# Blind restatement: direction of the cubic log-polynomial fit bias (B1)

**Reading of the claim.** In an exactly flat ΛCDM universe with `Ω ∈ [0.2, 0.4]`, any cubic
log-polynomial luminosity distance `D_L = ln 10 · (1/H) (x + a₂x² + a₃x³)`, `x = log₁₀(1+z)`,
that reproduces the exact distance modulus at `z = 3` and `z = 7` up to a single common
magnitude offset (within 0.05 mag at each redshift) must satisfy
`a₂ − lusA2 Ω < 7 log₁₀ 2 · (a₃ − lusA3 Ω)`.

**Modelling choices.**
* Cosmology: scale factor `a : ℝ → ℝ`, times `t₇ ≤ t₃ ≤ t₀` (emission at `z = 7`, emission at
  `z = 3`, now). On the whole interval `[t₇, t₀]`: `a > 0`, `a` differentiable, and
  `hubble a s = hubble a t₀ * √(Ω(1 + redshift a t₀ s)³ + 1 − Ω)`; `hubble a t₀ > 0`.
  The z = 3 emission time is required to lie in that interval (the plain-English "interval
  from the emission of the z = 7 source up to now" is read as containing it).
  Redshifts fixed by `redshift a t₀ t₃ = 3`, `redshift a t₀ t₇ = 7`.
* Exact distance: `lumDistFlat a t₀ t` (`c = 1`).
* Polynomial: `logPolyDL3 a₂ a₃ H z` with arbitrary real `a₂ a₃` and an arbitrary `H > 0`
  (not tied to `hubble a t₀`; any normalisation mismatch is absorbed anyway by the offset),
  evaluated at the literal redshifts `3` and `7`, assumed positive at both.
* Common offset: a real `δ` (universally quantified; equivalent to `∃ δ` in the hypothesis)
  with `|5 log₁₀(D_poly(z)/D_exact(z)) − δ| ≤ 0.05` for `z = 3, 7`. "Within 0.05 mag" is read
  non-strictly (`≤`), which is the weaker hypothesis. The ratio orientation is immaterial
  since `δ` is arbitrary in sign.
* Conclusion: `a₂ − lusA2 Ω < 7 · log₁₀ 2 · (a₃ − lusA3 Ω)`, strict, with
  `log₁₀ 2 = Real.logb 10 2`.
-/

namespace Work.Cosmography.B1DirBlind

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

theorem blind_direction (Ω : ℝ) (hΩ₁ : (1 / 5 : ℝ) ≤ Ω) (hΩ₂ : Ω ≤ 2 / 5)
    (a : ℝ → ℝ) (t₇ t₃ t₀ : ℝ) (h₇₃ : t₇ ≤ t₃) (h₃₀ : t₃ ≤ t₀)
    (hpos : ∀ s ∈ Set.Icc t₇ t₀, 0 < a s)
    (hdiff : ∀ s ∈ Set.Icc t₇ t₀, DifferentiableAt ℝ a s)
    (hH₀ : 0 < hubble a t₀)
    (hH : ∀ s ∈ Set.Icc t₇ t₀,
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω))
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7)
    (a₂ a₃ H : ℝ) (hHpos : 0 < H)
    (hP₃ : 0 < logPolyDL3 a₂ a₃ H 3) (hP₇ : 0 < logPolyDL3 a₂ a₃ H 7)
    (δ : ℝ)
    (hfit₃ : |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H 3 / lumDistFlat a t₀ t₃) - δ| ≤ 5 / 100)
    (hfit₇ : |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H 7 / lumDistFlat a t₀ t₇) - δ| ≤ 5 / 100) :
    a₂ - lusA2 Ω < 7 * Real.logb 10 2 * (a₃ - lusA3 Ω) := by
  sorry

end Work.Cosmography.B1DirBlind
