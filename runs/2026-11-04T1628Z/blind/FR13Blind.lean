import Mathlib

/-!
# Blind restatement: Farooq & Ratra 2013 (arXiv:1301.5243v1), flat ΛCDM best fit

Claim (Fig. 3 caption, φCDM at α = 0 = spatially-flat ΛCDM, prior H̄₀ ± σ = 68 ± 2.8):
best fit Ωm0 = 0.29, χ²_min = 18.24; transition redshift (Sec. 2) 0.698.

Likelihood: Sec. 2 of the paper defers to "Eq. 18 of Farooq et al. (2013)", which per the
paper's bibliography is Farooq, Mania & Ratra, arXiv:1211.4253.  There, Eq. (16) is
  L_H(p) = (2π σ_{H0}²)^{-1/2} ∫_0^∞ exp(-χ²_H(H0,p)/2) exp(-(H0-H̄0)²/(2σ_{H0}²)) dH0
and the text says "maximize L_H(p), or equivalently minimize χ²_H(p) = -2 ln L_H(p)".
Choices (see notes.md):
* H0 integrated over (0, ∞) (as in Eq. 16), not over ℝ.
* prior normalised by 1/√(2π σ²) (Eq. 16).  NB: the closed form Eq. (18) as printed carries
  1/√(2 α σ²) instead of the correct 1/√(4 α σ²); this shifts χ² by ln 2 but not the maximiser.
* χ²_min := -2 ln L_H at the maximiser.
* physically allowed range: 0 ≤ Ωm0 ≤ 1 (non-negative matter and dark-energy densities).
-/

namespace Blind.FR13

open Real MeasureTheory

/-- Table 1, rows `(z, H(z), σ_H)` in printed order (km s⁻¹ Mpc⁻¹). -/
noncomputable def table : Fin 28 → ℝ × ℝ × ℝ :=
  ![(0.070, 69, 19.6),
    (0.100, 69, 12),
    (0.120, 68.6, 26.2),
    (0.170, 83, 8),
    (0.179, 75, 4),
    (0.199, 75, 5),
    (0.200, 72.9, 29.6),
    (0.270, 77, 14),
    (0.280, 88.8, 36.6),
    (0.350, 76.3, 5.6),
    (0.352, 83, 14),
    (0.400, 95, 17),
    (0.440, 82.6, 7.8),
    (0.480, 97, 62),
    (0.593, 104, 13),
    (0.600, 87.9, 6.1),
    (0.680, 92, 8),
    (0.730, 97.3, 7.0),
    (0.781, 105, 12),
    (0.875, 125, 17),
    (0.880, 90, 40),
    (0.900, 117, 23),
    (1.037, 154, 20),
    (1.300, 168, 17),
    (1.430, 177, 18),
    (1.530, 140, 14),
    (1.750, 202, 40),
    (2.300, 224, 8)]

noncomputable def zObs (i : Fin 28) : ℝ := (table i).1
noncomputable def HObs (i : Fin 28) : ℝ := (table i).2.1
noncomputable def σObs (i : Fin 28) : ℝ := (table i).2.2

/-- Gaussian H0 prior parameters, H̄0 ± σ_{H0} = 68 ± 2.8 km s⁻¹ Mpc⁻¹. -/
noncomputable def H0bar : ℝ := 68
noncomputable def σH0 : ℝ := 2.8

/-- Dimensionless expansion rate of spatially-flat ΛCDM, E(z) = √(Ωm0 (1+z)³ + 1 − Ωm0). -/
noncomputable def E (Ωm z : ℝ) : ℝ := Real.sqrt (Ωm * (1 + z) ^ 3 + 1 - Ωm)

/-- Model Hubble parameter H(z) = H0 E(z). -/
noncomputable def Hth (H0 Ωm z : ℝ) : ℝ := H0 * E Ωm z

/-- χ²_H(H0, Ωm0) = Σ_i (H_th(z_i) − H_obs(z_i))² / σ_i²  (Farooq et al. 2013, Eq. 14). -/
noncomputable def chi2H (H0 Ωm : ℝ) : ℝ :=
  ∑ i : Fin 28, (Hth H0 Ωm (zObs i) - HObs i) ^ 2 / σObs i ^ 2

/-- Normalised Gaussian prior density on H0. -/
noncomputable def prior (H0 : ℝ) : ℝ :=
  1 / Real.sqrt (2 * π * σH0 ^ 2) * Real.exp (-(H0 - H0bar) ^ 2 / (2 * σH0 ^ 2))

/-- H0-marginalised likelihood (Farooq et al. 2013, Eq. 16): integral over H0 ∈ (0, ∞). -/
noncomputable def LH (Ωm : ℝ) : ℝ :=
  ∫ H0 in Set.Ioi (0 : ℝ), Real.exp (-chi2H H0 Ωm / 2) * prior H0

/-- χ²_H(p) := −2 ln L_H(p). -/
noncomputable def chi2Marg (Ωm : ℝ) : ℝ := -2 * Real.log (LH Ωm)

/-- Physically allowed range of Ωm0 in the flat model. -/
def allowed : Set ℝ := Set.Icc 0 1

/-- `Ωm` is a best fit: a maximiser of the marginalised likelihood over the allowed range. -/
def IsBestFit (Ωm : ℝ) : Prop := IsMaxOn LH allowed Ωm ∧ Ωm ∈ allowed

/-- Existence of a maximum-likelihood Ωm0. -/
theorem exists_bestFit : ∃ Ωm, IsBestFit Ωm := by
  sorry

/-- Main claim: every maximiser rounds to 0.29. (Numerically: 0.28779.) -/
theorem bestFit_rounds_to_029 :
    ∀ Ωm, IsBestFit Ωm → (0.285 : ℝ) ≤ Ωm ∧ Ωm < 0.295 := by
  sorry

/-- Printed χ²_min = 18.24 (to two decimals).  WARNING: with the Eq. 16 reading my numerics
give χ²_min = 18.1987 (Eq. 18 as printed: 17.5055), so I expect this to be FALSE as stated;
recorded for comparison only. -/
theorem chi2min_rounds_to_1824 :
    ∀ Ωm, IsBestFit Ωm → (18.235 : ℝ) ≤ chi2Marg Ωm ∧ chi2Marg Ωm < 18.245 := by
  sorry

/-! ## Transition redshift -/

/-- Hubble function of the flat model with H0 factored out. -/
noncomputable def Hfun (Ωm : ℝ) : ℝ → ℝ := fun z => E Ωm z

/-- Deceleration parameter q(z) = −1 + (1+z) H'(z)/H(z) (H0 cancels). -/
noncomputable def decel (Ωm z : ℝ) : ℝ :=
  -1 + (1 + z) * deriv (Hfun Ωm) z / Hfun Ωm z

/-- Closed-form transition redshift: q(z) = 0 ⇔ (1+z)³ = 2(1−Ωm0)/Ωm0. -/
noncomputable def zda (Ωm : ℝ) : ℝ := (2 * (1 - Ωm) / Ωm) ^ ((1 : ℝ) / 3) - 1

/-- Sanity/definitional lemma: for 0 < Ωm0 < 2/3, `zda` is the unique non-negative redshift
at which q vanishes, with deceleration before (higher z) and acceleration after. -/
theorem zda_spec (Ωm : ℝ) (h0 : 0 < Ωm) (h1 : Ωm < 2 / 3) :
    0 < zda Ωm ∧ decel Ωm (zda Ωm) = 0 ∧
    (∀ z, 0 ≤ z → z < zda Ωm → decel Ωm z < 0) ∧
    (∀ z, zda Ωm < z → 0 < decel Ωm z) := by
  sorry

/-- Implied by `bestFit_rounds_to_029` (zda is decreasing in Ωm0):
z_da ∈ (zda 0.295, zda 0.285] ≈ (0.6845, 0.7120]. Numerically z_da(best fit) = 0.7042. -/
theorem bestFit_zda_range :
    ∀ Ωm, IsBestFit Ωm → (0.684 : ℝ) < zda Ωm ∧ zda Ωm < 0.713 := by
  sorry

/-- Literal printed value for φCDM (α = 0), prior 68 ± 2.8: z_da = 0.698 (3 decimals).
WARNING: 0.698 equals zda(0.29) exactly-rounded (0.6981), i.e. the authors evaluated at the
rounded / grid best fit; at the true maximiser 0.28779 one gets 0.7042, so I expect this to be
FALSE as stated. -/
theorem bestFit_zda_rounds_to_0698 :
    ∀ Ωm, IsBestFit Ωm → (0.6975 : ℝ) ≤ zda Ωm ∧ zda Ωm < 0.6985 := by
  sorry

/-- What 0.698 actually is: the transition redshift of the rounded best fit Ωm0 = 0.29. -/
theorem zda_029 : (0.6975 : ℝ) ≤ zda 0.29 ∧ zda 0.29 < 0.6985 := by
  sorry

end Blind.FR13
