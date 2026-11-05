import Mathlib

/-!
# Moresco et al. 2016 (arXiv:1601.01701v2), Table 5 vs Eqs. 5.1, 5.3, 5.4, Table 4 (blind restatement)

Modelling choices:
* N: the paper does not state N for Table 5.  Table 4 has 30 points; Sec. 5.2 says the linear/piecewise
  analyses use 31 H/(1+z) points (30 + the H0 = 73 ± 2.4 point).  So N is quantified over {30, 31}
  (a: statement holds for both; b, c: witnesses work for both).
* k: oΛCDM k = 3 (H0, Ωm, zt), piecewise linear k = 4 (zt, two slopes, amplitude), linear fit k = 2
  (intercept, slope).
* Rounding: a printed value p is matched by a real x iff |x - p| ≤ ε, with ε ≤ 1/10 (generic; printed
  values have 2 decimals, so the honest tolerance is 0.005).  In (b),(c) the "below printed BIC" is
  strict against p - 0.005 (i.e. below the lowest value that rounds to p).
* −2 ln L_max is a free real in (a) (no model needed); in (b),(c) −2 ln L := χ², no additive constants.
* oΛCDM: H(z) = H0 sqrt(Ωm(1+z)^3 + Ωk(1+z)^2 + ΩΛ), Ωk = 1-Ωm-ΩΛ, ΩΛ from Eq. 5.2:
  zt = (2ΩΛ/Ωm)^(1/3) - 1, i.e. ΩΛ = Ωm (1+zt)^3 / 2.  Prior region Ωm ∈ [0,1], zt ∈ [0,1.5], and
  H0 is a free parameter (profiled / maximised, not marginalised), constrained by the Gaussian prior
  term ((H0-73)/2.4)^2 added to χ² (the prior acts as the 31st data point).  Also require radicand ≥ 0
  (otherwise sqrt = 0 in Lean would be an artefact); H0 ∈ ℝ unrestricted otherwise.
* Linear fit: the model is f(z) = H/(1+z) = a + b z, i.e. H(z) = (a + b z)(1+z), fitted to all 30 Table-4
  points (weights σ_H, since H/(1+z) with σ/(1+z) is the same χ²), plus the H0 prior term
  ((a-73)/2.4)^2 (f(0) = H0).  No parameter prior region.
* Data: Fin 30 → ℝ × ℝ × ℝ (z, H, σ), printed order, left column then right column.
-/

namespace Work.Data.Moresco16Blind

open Real

/-- Table 4 as printed: (z, H, σ_H). -/
noncomputable def table4 : Fin 30 → ℝ × ℝ × ℝ := ![
  (0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
  (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
  (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2),
  (0.44497, 92.8, 12.9),
  (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8), (0.781, 105, 12),
  (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20), (1.3, 168, 17),
  (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40), (1.965, 186.5, 50.4)]

/-- Eq. 5.3 (BIC). -/
noncomputable def BIC (m2lnL : ℝ) (k N : ℕ) : ℝ := m2lnL + k * Real.log N
/-- Eq. 5.3 (AIC). -/
noncomputable def AIC (m2lnL : ℝ) (k : ℕ) : ℝ := m2lnL + 2 * k
/-- Eq. 5.4 (AICc). -/
noncomputable def AICc (m2lnL : ℝ) (k N : ℕ) : ℝ :=
  AIC m2lnL k + 2 * k * (k + 1) / ((N : ℝ) - k - 1)

/-- Printed Table 5 values: (k, AICc, BIC). -/
noncomputable def table5 : Fin 3 → ℕ × ℝ × ℝ :=
  ![(3, 21.41, 25.71), (4, 23.99, 28.72), (2, 32.42, 35.29)]

/-- (a) For every row, for N ∈ {30,31}, tolerance ε ≤ 1/10: no single −2 ln L_max reproduces both
printed AICc and BIC. -/
theorem table5_inconsistent (i : Fin 3) (N : ℕ) (hN : N = 30 ∨ N = 31) (ε : ℝ) (hε : ε ≤ 1/10) :
    ¬ ∃ x : ℝ, |AICc x (table5 i).1 N - (table5 i).2.1| ≤ ε ∧
                |BIC x (table5 i).1 N - (table5 i).2.2| ≤ ε := by
  sorry

/-- χ² of the oΛCDM model (Eq. 5.1, 5.2) on Table 4, plus the Gaussian H0 prior 73 ± 2.4. -/
noncomputable def chi2OLCDM (H0 Om zt : ℝ) : ℝ :=
  (∑ i : Fin 30,
    ((((table4 i).2.1) -
      H0 * Real.sqrt (Om * (1 + (table4 i).1) ^ 3 +
        (1 - Om - Om * (1 + zt) ^ 3 / 2) * (1 + (table4 i).1) ^ 2 +
        Om * (1 + zt) ^ 3 / 2)) / (table4 i).2.2) ^ 2)
  + ((H0 - 73) / 2.4) ^ 2

/-- Radicand of Eq. 5.1 is nonnegative on all data redshifts (avoid junk sqrt = 0). -/
def radicandNonneg (Om zt : ℝ) : Prop :=
  ∀ i : Fin 30, 0 ≤ Om * (1 + (table4 i).1) ^ 3 +
        (1 - Om - Om * (1 + zt) ^ 3 / 2) * (1 + (table4 i).1) ^ 2 + Om * (1 + zt) ^ 3 / 2

/-- (b) oΛCDM: some parameters in the prior region give BIC below the printed 25.71. -/
theorem oLCDM_bic_below_printed (N : ℕ) (hN : N = 30 ∨ N = 31) :
    ∃ H0 Om zt : ℝ, Om ∈ Set.Icc (0:ℝ) 1 ∧ zt ∈ Set.Icc (0:ℝ) 1.5 ∧ radicandNonneg Om zt ∧
      BIC (chi2OLCDM H0 Om zt) 3 N < 25.71 - 0.005 := by
  sorry

/-- χ² of the straight line H/(1+z) = a + b z on Table 4, plus the H0 prior on a = f(0). -/
noncomputable def chi2Linear (a b : ℝ) : ℝ :=
  (∑ i : Fin 30,
    ((((table4 i).2.1) - (a + b * (table4 i).1) * (1 + (table4 i).1)) / (table4 i).2.2) ^ 2)
  + ((a - 73) / 2.4) ^ 2

/-- (c) Linear fit: some (a,b) give BIC below the printed 35.29. -/
theorem linear_bic_below_printed (N : ℕ) (hN : N = 30 ∨ N = 31) :
    ∃ a b : ℝ, BIC (chi2Linear a b) 2 N < 35.29 - 0.005 := by
  sorry

end Work.Data.Moresco16Blind
