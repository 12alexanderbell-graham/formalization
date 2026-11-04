import Checked.Cosmography.B1Truncation

/-!
# Blind restatement: the Risaliti–Lusso 2019 (Fig. 3) best-fit box cannot reproduce flat ΛCDM

Claim (in words). Risaliti & Lusso 2019, Fig. 3, fit the quasar+SN Hubble diagram with
`D_L = ln(10) (c/H) (x + a₂ x² + a₃ x³)`, `x = log₁₀(1+z)`, contour centre `(a₂, a₃) ≈ (3.46, 1.63)`
inside the box `a₂ ∈ [3.43, 3.49]`, `a₃ ∈ [1.57, 1.69]`. For every exactly flat ΛCDM universe with
`Ω_M ∈ [0, 1]`, no log-polynomial with coefficients in that box (any normalisation `H > 0`, positive
at the redshifts used) reproduces that universe's distance modulus to within `0.05` mag, up to a
common magnitude offset, at `1 + z = √2, 2√2, 4√2`.

## Modelling choices / ambiguities resolved

* **The universe.** A scale factor `a : ℝ → ℝ`, an observation time `t₀`, and an earliest time
  `T < t₀`. On the closed epoch `[T, t₀]` we assume `a > 0` and `a` differentiable (so that
  `hubble a t = ȧ/a` is the genuine expansion rate and the comoving integral in
  `lumDistFlat` is the integral of a continuous positive function).
* **Where the Friedmann law holds.** Only "over the relevant times": on `[T, t₀]`, which must
  contain the three emission times. We require
  `hubble a t = H₀ √(Ω_M (1 + z(t))³ + 1 − Ω_M)` with `z(t) = redshift a t₀ t`, for all
  `t ∈ [T, t₀]`, with `H₀ > 0` and `Ω_M ∈ [0, 1]`. Nothing is assumed before `T` or after `t₀`.
  (At `t = t₀` this gives `hubble a t₀ = H₀`, so `H₀` is the true Hubble constant.)
  Flatness is encoded by using `lumDistFlat` (flat-space luminosity distance, `c = 1`) and by the
  absence of a curvature term in the Friedmann law.
* **The redshifts used.** Emission times `t₁, t₂, t₃ ∈ [T, t₀]` with
  `redshift a t₀ tᵢ = √2 − 1, 2√2 − 1, 4√2 − 1` (i.e. `1 + z = √2, 2√2, 4√2`,
  equivalently `x = log₁₀ 2 · (1/2, 3/2, 5/2)`). The statement is universal in these times; their
  ordering follows from the hypotheses and is not assumed.
* **Distance modulus.** `μ = 5 log₁₀ D_L + const`; the constant (and the units of `D_L`, and
  `H₀` vs. `H`) all cancel into the offset, so only `5 log₁₀ D_L` is compared.
* **"Reproduce within 0.05 mag up to a common offset".** There EXISTS one real offset `δ`
  (the same for all three redshifts) with
  `|5 log₁₀ D_fit(zᵢ) − 5 log₁₀ D_ΛCDM(zᵢ) − δ| ≤ 0.05` for `i = 1, 2, 3`. The offset is
  existential (chosen freely, jointly with the fit), so the claim is the negation of
  `∃ a₂ a₃ H δ, …`. We use the non-strict `≤ 0.05`, which makes the negated claim the
  stronger (and the natural) reading of "within 0.05 mag".
* **Normalisation.** The fit's `H` is an arbitrary positive real, independent of `H₀`
  (it is in fact redundant with `δ`, but the claim says "any normalisation").
* **Positivity.** `Real.logb` of a non-positive number is junk in Mathlib (`logb 10 (-y) = logb 10 y`,
  `logb 10 0 = 0`), so the fitted `D_L` is required to be strictly positive at the three
  redshifts (as part of what a valid competing fit must satisfy, i.e. inside the existential).
  The ΛCDM `lumDistFlat` needs no positivity hypothesis: it is positive by the hypotheses on `a`.
* **The box.** Closed intervals `a₂ ∈ [3.43, 3.49]`, `a₃ ∈ [1.57, 1.69]`.

(Numerical sanity check, not part of the statement: the minimum over `Ω_M ∈ [0,1]` and the box of the
best achievable worst-case residual is ≈ 0.098 mag, attained near `Ω_M = 1`; at `Ω_M = 0.3` it is
≈ 0.28 mag. So the claim is expected to be true with margin.)
-/

namespace Work.Cosmography.B1FitRL19Blind

open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- No log-polynomial with `(a₂, a₃)` in the Risaliti–Lusso 2019 Fig. 3 box reproduces, up to a
common magnitude offset and within `0.05` mag, the distance modulus of any exactly flat ΛCDM
universe with `Ω_M ∈ [0,1]` at `1 + z = √2, 2√2, 4√2`. See the module docstring for the
modelling choices. -/
theorem rl19_box_cannot_fit_flatLCDM
    (a : ℝ → ℝ) (Ω H₀ T t₀ t₁ t₂ t₃ : ℝ)
    (hΩ : Ω ∈ Set.Icc (0 : ℝ) 1) (hH₀ : 0 < H₀) (hT : T < t₀)
    (ha_pos : ∀ t ∈ Set.Icc T t₀, 0 < a t)
    (ha_diff : ∀ t ∈ Set.Icc T t₀, DifferentiableAt ℝ a t)
    (hFried : ∀ t ∈ Set.Icc T t₀,
      hubble a t = H₀ * Real.sqrt (Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω))
    (ht₁ : t₁ ∈ Set.Icc T t₀) (ht₂ : t₂ ∈ Set.Icc T t₀) (ht₃ : t₃ ∈ Set.Icc T t₀)
    (hz₁ : redshift a t₀ t₁ = Real.sqrt 2 - 1)
    (hz₂ : redshift a t₀ t₂ = 2 * Real.sqrt 2 - 1)
    (hz₃ : redshift a t₀ t₃ = 4 * Real.sqrt 2 - 1) :
    ¬ ∃ a₂ a₃ H δ : ℝ,
      a₂ ∈ Set.Icc (3.43 : ℝ) 3.49 ∧ a₃ ∈ Set.Icc (1.57 : ℝ) 1.69 ∧ 0 < H ∧
      0 < logPolyDL3 a₂ a₃ H (Real.sqrt 2 - 1) ∧
      0 < logPolyDL3 a₂ a₃ H (2 * Real.sqrt 2 - 1) ∧
      0 < logPolyDL3 a₂ a₃ H (4 * Real.sqrt 2 - 1) ∧
      |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (Real.sqrt 2 - 1))
          - 5 * Real.logb 10 (lumDistFlat a t₀ t₁) - δ| ≤ 0.05 ∧
      |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (2 * Real.sqrt 2 - 1))
          - 5 * Real.logb 10 (lumDistFlat a t₀ t₂) - δ| ≤ 0.05 ∧
      |5 * Real.logb 10 (logPolyDL3 a₂ a₃ H (4 * Real.sqrt 2 - 1))
          - 5 * Real.logb 10 (lumDistFlat a t₀ t₃) - δ| ≤ 0.05 := by
  sorry

end Work.Cosmography.B1FitRL19Blind
