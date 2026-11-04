import Mathlib

/-!
# A data claim, certified (THE RESULT part 1, "test suites for scientific claims"):
# the best-fit matter density of the Farooq & Ratra 2013 H(z) compilation

**Question.** Farooq & Ratra 2013 (arXiv:1301.5243v1, ApJL 766, L7) list 28 measurements
(z, H(z), σ_H) in their Table 1 and fit expansion laws to them. Their Sec. 2: the likelihood of
the model parameters is obtained by *integrating* exp(−χ²_H/2) times a Gaussian prior on the
Hubble constant H₀ (H̄₀ ± σ = 68 ± 2.8 or 73.8 ± 2.4 km/s/Mpc) over H₀, and the best fit
maximises it. For the spatially flat law H(z) = H₀ √(Ω(1+z)³ + 1 − Ω) (their φCDM at α = 0,
Fig. 3 caption) they print best fits Ω = 0.29 [0.25] with χ²_min = 18.24 [20.64] and, in the
text, transition redshifts 0.698 [0.817].

A floating-point fit is a claim nobody can check without redoing it. Here the claim is a
theorem about the statistic itself, computed from the transcribed table with exact rational
arithmetic: every minimiser of the marginalised χ² over Ω ∈ [0, 1] lies in a stated interval,
and a minimiser exists.

**Definitions** (conventions as in the paper; units km/s/Mpc throughout):
* `fr13Table i = (zᵢ, Hᵢ, σᵢ)`: Table 1, rows in printed order (PRINTED).
* `chiSqHz tbl H₀ Ω = Σᵢ ((H₀ √(Ω(1+zᵢ)³ + 1 − Ω) − Hᵢ)/σᵢ)²`.
* `margChiSq tbl H̄ σ Ω = −2 log ∫ exp(−χ²/2) · N(H₀; H̄, σ²) dH₀`, the integral over all real H₀
  and N the normalised Gaussian density. (The paper does not state the integration range; over
  H₀ > 0 instead the integral changes by a relative amount below 10⁻¹⁰⁰ here, not proved.)

**What is stated here** (frozen before proof, annex 40.1):
1. `fr13_bestfit68`, `fr13_bestfit738`: every Ω ∈ [0, 1] minimising `margChiSq fr13Table 68 2.8`
   [resp. `73.8 2.4`] over [0, 1] satisfies 0.2875 < Ω < 0.2881 [0.2531 < Ω < 0.2537].
2. `fr13_exists68`, `fr13_exists738`: such a minimiser exists.
3. `fr13_minval68`, `fr13_minval738`: at every minimiser, 18.19 < margChiSq < 18.21
   [20.61 < margChiSq < 20.62].
4. `fr13_zda68`, `fr13_zda738`: at every minimiser, the z > −1 with Ω(1+z)³ = 2(1 − Ω)
   (where the flat law's deceleration changes sign) satisfies 0.703 < z < 0.706 [0.805 < z < 0.808].
-/

namespace Work.Data.FR13
open MeasureTheory

/-- Farooq & Ratra 2013 (arXiv:1301.5243v1), Table 1, transcribed in printed order: row `i` is
(redshift zᵢ, measured expansion rate Hᵢ in km/s/Mpc, its one-standard-deviation error σᵢ). -/
noncomputable def fr13Table : Fin 28 → ℝ × ℝ × ℝ :=
  ![(0.070, 69, 19.6), (0.100, 69, 12), (0.120, 68.6, 26.2), (0.170, 83, 8),
    (0.179, 75, 4), (0.199, 75, 5), (0.200, 72.9, 29.6), (0.270, 77, 14),
    (0.280, 88.8, 36.6), (0.350, 76.3, 5.6), (0.352, 83, 14), (0.400, 95, 17),
    (0.440, 82.6, 7.8), (0.480, 97, 62), (0.593, 104, 13), (0.600, 87.9, 6.1),
    (0.680, 92, 8), (0.730, 97.3, 7.0), (0.781, 105, 12), (0.875, 125, 17),
    (0.880, 90, 40), (0.900, 117, 23), (1.037, 154, 20), (1.300, 168, 17),
    (1.430, 177, 18), (1.530, 140, 14), (1.750, 202, 40), (2.300, 224, 8)]

/-- Chi-square of the law H(z) = H₀ √(Ω(1+z)³ + 1 − Ω) against a table of rows (z, H, σ):
the sum over rows of ((H₀ √(Ω(1+z)³ + 1 − Ω) − H)/σ)². -/
noncomputable def chiSqHz {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (H₀ Ω : ℝ) : ℝ :=
  ∑ i, ((H₀ * √(Ω * (1 + (tbl i).1) ^ 3 + 1 - Ω) - (tbl i).2.1) / (tbl i).2.2) ^ 2

/-- Marginalised chi-square with a Gaussian prior of mean `Hbar` and standard deviation `σ` on
H₀: minus twice the logarithm of the integral over all real H₀ of exp(−χ²/2) times the
normalised Gaussian density exp(−(H₀ − Hbar)²/(2σ²))/√(2πσ²). -/
noncomputable def margChiSq {n : ℕ} (tbl : Fin n → ℝ × ℝ × ℝ) (Hbar σ Ω : ℝ) : ℝ :=
  -2 * Real.log (∫ H₀ : ℝ, Real.exp (-chiSqHz tbl H₀ Ω / 2) *
    (Real.exp (-(H₀ - Hbar) ^ 2 / (2 * σ ^ 2)) / √(2 * Real.pi * σ ^ 2)))

/-! ### Frozen statements -/

/-- With the prior 68 ± 2.8 on H₀, every Ω in [0, 1] at which the marginalised chi-square of
the Farooq–Ratra 2013 table is smallest among all Ω′ in [0, 1] lies strictly between 0.2875
and 0.2881. -/
theorem fr13_bestfit68 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω') :
    0.2875 < Ω ∧ Ω < 0.2881 := by
  sorry

/-- With the prior 73.8 ± 2.4 on H₀, every Ω in [0, 1] at which the marginalised chi-square of
the Farooq–Ratra 2013 table is smallest among all Ω′ in [0, 1] lies strictly between 0.2531
and 0.2537. -/
theorem fr13_bestfit738 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1,
      margChiSq fr13Table 73.8 2.4 Ω ≤ margChiSq fr13Table 73.8 2.4 Ω') :
    0.2531 < Ω ∧ Ω < 0.2537 := by
  sorry

/-- With the prior 68 ± 2.8, the marginalised chi-square of the Farooq–Ratra 2013 table attains
its smallest value over Ω in [0, 1]: there is a minimiser. -/
theorem fr13_exists68 : ∃ Ω ∈ Set.Icc (0 : ℝ) 1,
    ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω' := by
  sorry

/-- With the prior 73.8 ± 2.4, the marginalised chi-square of the Farooq–Ratra 2013 table
attains its smallest value over Ω in [0, 1]: there is a minimiser. -/
theorem fr13_exists738 : ∃ Ω ∈ Set.Icc (0 : ℝ) 1,
    ∀ Ω' ∈ Set.Icc (0 : ℝ) 1,
      margChiSq fr13Table 73.8 2.4 Ω ≤ margChiSq fr13Table 73.8 2.4 Ω' := by
  sorry

/-- With the prior 68 ± 2.8, the smallest value over Ω in [0, 1] of the marginalised
chi-square of the Farooq–Ratra 2013 table lies strictly between 18.19 and 18.21. -/
theorem fr13_minval68 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω') :
    18.19 < margChiSq fr13Table 68 2.8 Ω ∧ margChiSq fr13Table 68 2.8 Ω < 18.21 := by
  sorry

/-- With the prior 73.8 ± 2.4, the smallest value over Ω in [0, 1] of the marginalised
chi-square of the Farooq–Ratra 2013 table lies strictly between 20.61 and 20.62. -/
theorem fr13_minval738 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1,
      margChiSq fr13Table 73.8 2.4 Ω ≤ margChiSq fr13Table 73.8 2.4 Ω') :
    20.61 < margChiSq fr13Table 73.8 2.4 Ω ∧ margChiSq fr13Table 73.8 2.4 Ω < 20.62 := by
  sorry

/-- With the prior 68 ± 2.8, at every minimiser Ω over [0, 1] of the marginalised chi-square
of the Farooq–Ratra 2013 table, the z > −1 solving Ω(1+z)³ = 2(1 − Ω) lies strictly between
0.703 and 0.706. -/
theorem fr13_zda68 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1, margChiSq fr13Table 68 2.8 Ω ≤ margChiSq fr13Table 68 2.8 Ω')
    (z : ℝ) (hz : -1 < z) (hda : Ω * (1 + z) ^ 3 = 2 * (1 - Ω)) :
    0.703 < z ∧ z < 0.706 := by
  sorry

/-- With the prior 73.8 ± 2.4, at every minimiser Ω over [0, 1] of the marginalised chi-square
of the Farooq–Ratra 2013 table, the z > −1 solving Ω(1+z)³ = 2(1 − Ω) lies strictly between
0.805 and 0.808. -/
theorem fr13_zda738 (Ω : ℝ) (hΩ₀ : 0 ≤ Ω) (hΩ₁ : Ω ≤ 1)
    (hmin : ∀ Ω' ∈ Set.Icc (0 : ℝ) 1,
      margChiSq fr13Table 73.8 2.4 Ω ≤ margChiSq fr13Table 73.8 2.4 Ω')
    (z : ℝ) (hz : -1 < z) (hda : Ω * (1 + z) ^ 3 = 2 * (1 - Ω)) :
    0.805 < z ∧ z < 0.808 := by
  sorry

end Work.Data.FR13
