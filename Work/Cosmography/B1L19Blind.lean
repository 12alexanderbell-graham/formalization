import Checked.Cosmography.B1Truncation

/-!
# Blind restatement: shape residual of the Lusso et al. 2019 quartic fits against flat ΛCDM

Source: Lusso et al. 2019, A&A 628, L4 (arXiv:1907.07692v4). Eq. (7):
`D_L(z) = k ln(10) (c/H₀) [x + a₂x² + a₃x³ + a₄x⁴]`, `x = log₁₀(1+z)`; Table 2 best fits
(central, +σ/−σ):
* SNe + quasars + GRBs ("sqg"): `a₂ = 3.205 (+0.165/−0.162)`, `a₃ = 3.564 (+0.916/−0.938)`,
  `a₄ = −2.510 (+1.595/−1.536)`;
* SNe + quasars ("sq"): `a₂ = 3.075 (+0.172/−0.169)`, `a₃ = 4.466 (+1.013/−1.040)`,
  `a₄ = −3.716 (+1.922/−1.852)`.

Claims: in every flat ΛCDM universe with `Ω_M ∈ [0, 1]`, with sources at `1+z = 2√2` and
`1+z = 4√2`, and for every normalisation of the fit, the residual
`5 log₁₀(d_L^exact / D_L^fit)` at `1+z = 4√2` exceeds the one at `1+z = 2√2`
1. by more than 0.35 mag for the sq central quartic (`blind_sq_central`);
2. by more than 0.3 mag for the sqg central quartic (`blind_sqg_central`);
3. strictly, for every quartic in the closed ±1σ coordinate box of sq (`blind_sq_box`);
4. strictly, for every quartic in the closed ±1σ coordinate box of sqg (`blind_sqg_box`).

## Modelling choices (referee note)

1. **Conventions.** Those of `Checked.Cosmography`: `c = 1`, `hubble a t = deriv a t / a t`,
   `redshift a t₀ t = a t₀ / a t − 1`, `lumDistFlat a t₀ t = a(t₀)(1+z) ∫_t^{t₀} 1/a`.
   The exact distance is `lumDistFlat a t₀ t` of the scale factor itself, not a closed-form
   ΛCDM integral; the bridge to the integral (`B1.lumDistFlat_flatLCDM`) is proof work.
2. **"A flat ΛCDM universe"** (`FlatLCDMOn Ω a t₁ t₀`): `H₀ := hubble a t₀ > 0`, and for every
   `s ∈ [t₁, t₀]`: `a s > 0` and the Friedmann law
   `hubble a s = H₀ √(Ω (1 + redshift a t₀ s)³ + 1 − Ω)`. `Ω ∈ [0, 1]` is a separate
   hypothesis of each theorem (both endpoints included: Ω = 0 is de Sitter, Ω = 1 is
   Einstein–de Sitter). Radiation is neglected, as in the claim.
3. **Epoch.** The law is assumed only on `[min t₂ t₄, t₀]` (the past interval reaching both
   sources), not globally, and not merely near `t₀`. The source times only need `t₂ ≤ t₀`,
   `t₄ ≤ t₀`; their mutual order is not assumed (it follows from the law). Sources are given
   by `redshift a t₀ t₂ = 2√2 − 1` and `redshift a t₀ t₄ = 4√2 − 1`.
4. **No differentiability hypothesis.** It is redundant: on the interval `a s > 0`, `a t₀ > 0`,
   so `1 + z > 0`, the radicand `1 + Ω((1+z)³ − 1) ≥ min(1, (1+z)³) > 0`, hence
   `hubble a s > 0`, hence `deriv a s ≠ 0`, which (Mathlib's junk `deriv = 0` off the
   differentiable locus) forces `DifferentiableAt ℝ a s`. Positivity of `a` is NOT redundant
   (with `a s = 0` the junk values `a t₀ / 0 = 0`, `deriv a s / 0 = 0` satisfy the law at
   Ω = 1), and `0 < hubble a t₀` is NOT redundant (with `H₀ = 0` the law only says
   `deriv a = 0` junk-wise, which does not constrain a nowhere-differentiable `a`).
5. **Fitted distance** (`quarticDL k a₂ a₃ a₄ H z`): `k · ln 10 / H · (x + a₂x² + a₃x³ + a₄x⁴)`,
   `x = logb 10 (1+z)`, evaluated at the model redshift `redshift a t₀ t` of the source
   (equal to the literal `2√2 − 1`, `4√2 − 1` by hypothesis). The fit's `H` is a free
   parameter, independent of the universe's `hubble a t₀` ("normalisation is free"); `k` is
   free too. Both are assumed **positive** (`0 < k`, `0 < H`): a positive fitted distance is
   the physical reading; the central quartics and every quartic in both boxes are positive at
   `x = log₁₀(2√2)` and `x = log₁₀(4√2)` (numerically, the minimum of the polynomial factor
   over the box corners is ≈ 1.13 / 2.07 (sq) and ≈ 1.15 / 2.30 (sqg) at the near / far
   source; the factor is affine in the coefficients), so no separate positivity hypothesis on the
   polynomial is needed. (Since `Real.log` is `log |·|`, the statements would also hold for
   any `k ≠ 0`, `H ≠ 0` by junk-value symmetry; this is deliberately not exploited.)
6. **Magnitude offset.** A common magnitude zero-point `δ` added to both residuals cancels
   identically in the difference, so it is omitted from the statements. `k` and `H` enter
   only through `k / H`, which also cancels in the difference; they are kept separate to
   match Eq. (7).
7. **Residual** at a source at time `t`: `5 * Real.logb 10 (lumDistFlat a t₀ t / D_fit)`, i.e.
   the exact distance modulus minus the fitted one (sign: positive when the fit
   underestimates). "Residual at 4√2 exceeds residual at 2√2 by more than c" is
   `c < resid(t₄) − resid(t₂)`; "strictly larger" is `resid(t₂) < resid(t₄)`.
8. **Coefficients.** Printed decimals, read as exact rationals (`3.075 = 3075/1000` etc.).
   **Boxes** are closed coordinate boxes `[centre − σ₋, centre + σ₊]` in each of `a₂, a₃, a₄`
   separately (not an error ellipse; correlations ignored, as the claim says), with the
   endpoints written as `centre − σ₋`, `centre + σ₊` literally. Closed boxes give the
   stronger statement.
9. **Uniformity.** Every theorem is uniform in `Ω ∈ [0, 1]`, in the scale factor, in `k`, `H`,
   and (box theorems) in the coefficients; all quantifiers are universal, with no existential
   choice of normalisation.

## Junk-value issues

* `Real.logb 10 y` for `y ≤ 0`: `Real.logb 10 0 = 0`, and for `y < 0` it is `logb 10 |y|`.
  With `k, H > 0`, positive polynomial values and `lumDistFlat > 0` (true in the model,
  proof work), all arguments are positive, so no junk is hit. With `k = 0` (excluded) both
  residuals would be the junk `logb 10 0 = 0` and the claims would fail.
* Division by zero: `quarticDL` divides by `H` (`H > 0` assumed); the residual divides by
  `D_fit` (nonzero as above); `redshift` divides by `a t` (`a > 0` on the interval);
  `hubble` divides by `a t` (same).
* `√` of a negative number is `0`; the radicand of the Friedmann law is positive under the
  hypotheses (item 4), so no junk there.
* `logb 10 (1 + z)` at `1 + z = 2√2, 4√2 > 0`: no junk.

Numerical sanity check (Simpson, not part of the statements): the sq central shape residual
decreases in Ω from ≈ 1.63 (Ω = 0) to ≈ 0.379 (Ω = 1); sqg from ≈ 1.57 to ≈ 0.318; the
minimum over the boxes (attained at vertices, the ratio `P(x₁)/P(x₂)` being linear-fractional
in the coefficients) is ≈ 0.029 (sq) and ≈ 0.023 (sqg), at Ω = 1.
-/

namespace Work.Cosmography.B1L19Blind

open Checked.Cosmography Checked.Cosmography.BambaY

/-- The fourth-order log-polynomial luminosity distance of Lusso et al. 2019, Eq. (7), with
`c = 1`: `D_L = k ln(10) / H · (x + a₂x² + a₃x³ + a₄x⁴)`, `x = log₁₀(1+z)`. -/
noncomputable def quarticDL (k a₂ a₃ a₄ H z : ℝ) : ℝ :=
  k * Real.log 10 / H *
    (Real.logb 10 (1 + z) + a₂ * Real.logb 10 (1 + z) ^ 2 + a₃ * Real.logb 10 (1 + z) ^ 3 +
      a₄ * Real.logb 10 (1 + z) ^ 4)

/-- Flat ΛCDM with matter fraction `Ω` on the epoch `[t₁, t₀]`, observed at `t₀`:
`H₀ = hubble a t₀ > 0`, `a > 0` and `H = H₀ √(Ω(1+z)³ + 1 − Ω)` at every `s ∈ [t₁, t₀]`. -/
def FlatLCDMOn (Ω : ℝ) (a : ℝ → ℝ) (t₁ t₀ : ℝ) : Prop :=
  0 < hubble a t₀ ∧
    ∀ s ∈ Set.Icc t₁ t₀, 0 < a s ∧
      hubble a s = hubble a t₀ * √(Ω * (1 + redshift a t₀ s) ^ 3 + 1 - Ω)

/-- Distance-modulus residual of a fitted distance `D` against an exact distance `d`:
`5 log₁₀(d / D)`. -/
noncomputable def resid (d D : ℝ) : ℝ := 5 * Real.logb 10 (d / D)

/-- **Claim 1 (SNe + quasars, central).** -/
theorem blind_sq_central (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    (35 / 100 : ℝ) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k 3.075 4.466 (-3.716) H (redshift a t₀ t₄)) -
      resid (lumDistFlat a t₀ t₂) (quarticDL k 3.075 4.466 (-3.716) H (redshift a t₀ t₂)) := by
  sorry

/-- **Claim 2 (SNe + quasars + GRBs, central).** -/
theorem blind_sqg_central (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    (3 / 10 : ℝ) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k 3.205 3.564 (-2.510) H (redshift a t₀ t₄)) -
      resid (lumDistFlat a t₀ t₂) (quarticDL k 3.205 3.564 (-2.510) H (redshift a t₀ t₂)) := by
  sorry

/-- **Claim 3 (SNe + quasars, ±1σ box).** -/
theorem blind_sq_box (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (a₂ a₃ a₄ : ℝ)
    (ha₂ : a₂ ∈ Set.Icc (3.075 - 0.169) (3.075 + 0.172))
    (ha₃ : a₃ ∈ Set.Icc (4.466 - 1.040) (4.466 + 1.013))
    (ha₄ : a₄ ∈ Set.Icc (-3.716 - 1.852) (-3.716 + 1.922))
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    resid (lumDistFlat a t₀ t₂) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₂)) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₄)) := by
  sorry

/-- **Claim 4 (SNe + quasars + GRBs, ±1σ box).** -/
theorem blind_sqg_box (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (a : ℝ → ℝ) (t₂ t₄ t₀ : ℝ) (h₂ : t₂ ≤ t₀) (h₄ : t₄ ≤ t₀)
    (hΛ : FlatLCDMOn Ω a (min t₂ t₄) t₀)
    (hz₂ : redshift a t₀ t₂ = 2 * √2 - 1) (hz₄ : redshift a t₀ t₄ = 4 * √2 - 1)
    (a₂ a₃ a₄ : ℝ)
    (ha₂ : a₂ ∈ Set.Icc (3.205 - 0.162) (3.205 + 0.165))
    (ha₃ : a₃ ∈ Set.Icc (3.564 - 0.938) (3.564 + 0.916))
    (ha₄ : a₄ ∈ Set.Icc (-2.510 - 1.536) (-2.510 + 1.595))
    (k H : ℝ) (hk : 0 < k) (hH : 0 < H) :
    resid (lumDistFlat a t₀ t₂) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₂)) <
      resid (lumDistFlat a t₀ t₄) (quarticDL k a₂ a₃ a₄ H (redshift a t₀ t₄)) := by
  sorry

end Work.Cosmography.B1L19Blind
