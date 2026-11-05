import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Checked.Data.Moresco16Certs

/-!
# A data claim tested (THE RESULT part 1, "test suites for scientific claims"):
# the information criteria printed by Moresco et al. 2016

Promoted from `Work/Data/Moresco16.lean` (run 2026-11-05T0428Z: freeze, proof, referee) in run
2026-11-05T1028Z: statements and proofs unchanged, specific Mathlib imports, prose rewritten for the
prose rules (the Work module doc keeps the full discussion).

**Source.** Moresco et al. 2016 (arXiv identifier in the docstring of `m16Table`). Their Table 4
lists thirty cosmic-chronometer measurements (z, H(z), σ_H) in km/s/Mpc. Their Sec. 5 fits them,
with a Gaussian prior on H₀ entering χ² as one more term, by the open-universe law H₀ √E²
(E² = `e2OL`: matter, cosmological constant, and the remainder 1 − Ω_m − Ω_Λ), by a piecewise-linear
and by a straight-line law for H/(1+z); their Table 5 prints AICc and BIC for each fit.

**What is stated here** (frozen before proof). Writing c for −2 ln L_max:
1. `table5_oL_inconsistent`, `table5_pw_inconsistent`, `table5_line_inconsistent`: in each row of
   Table 5, for every real N in the stated range (no convention for N assumed) and every c, the
   printed AICc (read as AIC + 2k(k + 1)/(N − k − 1)) and the printed BIC are not values for one and
   the same maximum likelihood.
2. `oL_bic_exceeds`: there is a point of the paper's prior region at which χ² + 3 ln N lies below the
   printed oLCDM BIC (minus rounding) for every N up to 35, so that BIC exceeds the BIC of the fit.
3. `line_bic_exceeds`: the same for the straight line.

**Definitions.** `m16Table` (PRINTED; an independent second reading agrees entry by entry,
`Checked.Trust.Transcriptions.agree_m16Table`); `e2OL`, `chiSqOL`, `chiSqLine` (FORMULA; blind second
formulations agree, `Checked/Trust/FormulationsM16.lean`).

**Referee corrections** (`runs/2026-11-05T0428Z/referee_m16.md`, STANDS-WITH-CORRECTIONS). Claim 1
holds for the column headed AICc read as the corrected criterion. If that column holds the
uncorrected AIC with N = 31, the oLCDM and linear rows are internally consistent; the piecewise row
is inconsistent under every reading tried. Claims 2 and 3 do not depend on that reading. No stated
conclusion of the paper changes.
-/

namespace Checked.Data.Moresco16
open Real

/-- Table 4 of Moresco et al. 2016 (arXiv:1601.01701v2): the thirty (z, H(z), σ_H) cosmic
chronometer measurements in km/s/Mpc, left column then right column, as printed. -/
noncomputable def m16Table : Fin 30 → ℝ × ℝ × ℝ :=
  ![(0.07, 69.0, 19.6), (0.09, 69, 12), (0.12, 68.6, 26.2), (0.17, 83, 8), (0.179, 75, 4),
    (0.199, 75, 5), (0.20, 72.9, 29.6), (0.27, 77, 14), (0.28, 88.8, 36.6), (0.352, 83, 14),
    (0.3802, 83, 13.5), (0.4, 95, 17), (0.4004, 77, 10.2), (0.4247, 87.1, 11.2),
    (0.44497, 92.8, 12.9), (0.4783, 80.9, 9), (0.48, 97, 62), (0.593, 104, 13), (0.68, 92, 8),
    (0.781, 105, 12), (0.875, 125, 17), (0.88, 90, 40), (0.9, 117, 23), (1.037, 154, 20),
    (1.3, 168, 17), (1.363, 160, 33.6), (1.43, 177, 18), (1.53, 140, 14), (1.75, 202, 40),
    (1.965, 186.5, 50.4)]

/-- The squared dimensionless expansion rate E² at z of Eq. 5.1 (matter fraction Ω_m,
cosmological-constant fraction Ω_Λ, remainder 1 − Ω_m − Ω_Λ):
Ω_m (1+z)³ + (1 − Ω_m − Ω_Λ)(1+z)² + Ω_Λ (Moresco et al. 2016, Eq. 5.1). -/
noncomputable def e2OL (Ωm ΩΛ z : ℝ) : ℝ :=
  Ωm * (1 + z) ^ 3 + (1 - Ωm - ΩΛ) * (1 + z) ^ 2 + ΩΛ

/-- χ² of the law H₀ √E² (E² = `e2OL`) against the thirty measurements of Table 4, plus the
Gaussian prior term (H₀ − 73)²/2.4² (Moresco et al. 2016, Sec. 5.2). -/
noncomputable def chiSqOL (H0 Ωm ΩΛ : ℝ) : ℝ :=
  (∑ i, (H0 * Real.sqrt (e2OL Ωm ΩΛ (m16Table i).1) - (m16Table i).2.1) ^ 2 /
    (m16Table i).2.2 ^ 2) + (H0 - 73) ^ 2 / 2.4 ^ 2

/-- χ² of the straight line f(z) = a + b z against the values H/(1+z) of Table 4 with errors
σ_H/(1+z), plus the point f(0) = 73 ± 2.4 (Moresco et al. 2016, Sec. 5.2, linear fit). -/
noncomputable def chiSqLine (a b : ℝ) : ℝ :=
  (∑ i, ((a + b * (m16Table i).1) - (m16Table i).2.1 / (1 + (m16Table i).1)) ^ 2 /
    ((m16Table i).2.2 / (1 + (m16Table i).1)) ^ 2) + (a - 73) ^ 2 / 2.4 ^ 2

set_option maxHeartbeats 8000000 in
open Checked.Data.Moresco16Certs in
/-- Each χ² term at (72.2865, 0.43617, 0.98144) is at most the certificate `cU i` (helper). -/
theorem term_bound (i : Fin 30) :
    (72.2865 * Real.sqrt (e2OL 0.43617 0.98144 (m16Table i).1) - (m16Table i).2.1) ^ 2 /
      (m16Table i).2.2 ^ 2 ≤ cU i := by
  apply term_le (s := cS i) (ε := 1 / 10 ^ 9) (A := cA i) <;> fin_cases i <;>
    norm_num [cS, cA, cU, e2OL, m16Table]

/-- ln 31 < 3.4346 (helper). -/
theorem log31_lt : Real.log 31 < 3.4346 := by
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have h : Real.log (31 / 32) ≤ 31 / 32 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have e : Real.log 31 = Real.log (31 / 32) + Real.log 32 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have := Real.log_two_lt_d9
  norm_num at this
  linarith

/-- ln 35 < 3.56 (helper). -/
theorem log35_lt : Real.log 35 < 3.56 := by
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have h : Real.log (35 / 32) ≤ 35 / 32 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have e : Real.log 35 = Real.log (35 / 32) + Real.log 32 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have := Real.log_two_lt_d9
  norm_num at this
  linarith

/-- Table 5, row oLCDM (k = 3): for every N with 4 < N ≤ 31 and every value c of −2 ln L_max,
if c + 6 + 24/(N − 4) is within 0.005 of the printed AICc 21.41, then c + 3 ln N differs from
the printed BIC 25.71 by more than 0.005. -/
theorem table5_oL_inconsistent (N c : ℝ) (hN : 4 < N) (hN31 : N ≤ 31)
    (hA : |c + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) - 21.41| ≤ 0.005) :
    0.005 < |c + 3 * Real.log N - 25.71| := by
  have hN0 : 0 < N := by linarith
  have hl : Real.log N ≤ Real.log 31 := Real.log_le_log hN0 hN31
  have hq : (24 : ℝ) / 27 ≤ 2 * 3 * (3 + 1) / (N - 3 - 1) := by
    rw [show (2 : ℝ) * 3 * (3 + 1) = 24 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h31 := log31_lt
  have hA2 := (abs_le.1 hA).2
  rw [lt_abs]; right
  norm_num at hq hA2 h31 ⊢
  linarith

/-- Table 5, piecewise-linear row (k = 4): for every N with 5 < N ≤ 31 and every value c of
−2 ln L_max, if c + 8 + 40/(N − 5) is within 0.005 of the printed AICc 23.99, then
c + 4 ln N differs from the printed BIC 28.72 by more than 0.005. -/
theorem table5_pw_inconsistent (N c : ℝ) (hN : 5 < N) (hN31 : N ≤ 31)
    (hA : |c + 2 * 4 + 2 * 4 * (4 + 1) / (N - 4 - 1) - 23.99| ≤ 0.005) :
    0.005 < |c + 4 * Real.log N - 28.72| := by
  have hN0 : 0 < N := by linarith
  have hl : Real.log N ≤ Real.log 31 := Real.log_le_log hN0 hN31
  have hq : (40 : ℝ) / 26 ≤ 2 * 4 * (4 + 1) / (N - 4 - 1) := by
    rw [show (2 : ℝ) * 4 * (4 + 1) = 40 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h31 := log31_lt
  have hA2 := (abs_le.1 hA).2
  rw [lt_abs]; right
  norm_num at hq hA2 h31 ⊢
  linarith

/-- Table 5, linear row (k = 2): for every N with 3 < N ≤ 31 and every value c of −2 ln L_max,
if c + 4 + 12/(N − 3) is within 0.005 of the printed AICc 32.42, then c + 2 ln N differs from
the printed BIC 35.29 by more than 0.005. -/
theorem table5_line_inconsistent (N c : ℝ) (hN : 3 < N) (hN31 : N ≤ 31)
    (hA : |c + 2 * 2 + 2 * 2 * (2 + 1) / (N - 2 - 1) - 32.42| ≤ 0.005) :
    0.005 < |c + 2 * Real.log N - 35.29| := by
  have hN0 : 0 < N := by linarith
  have hl : Real.log N ≤ Real.log 31 := Real.log_le_log hN0 hN31
  have hq : (12 : ℝ) / 28 ≤ 2 * 2 * (2 + 1) / (N - 2 - 1) := by
    rw [show (2 : ℝ) * 2 * (2 + 1) = 12 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have h31 := log31_lt
  have hA2 := (abs_le.1 hA).2
  rw [lt_abs]; right
  norm_num at hq hA2 h31 ⊢
  linarith

/-- There are H₀, Ω_m, Ω_Λ in the paper's prior region (0 ≤ Ω_m ≤ 1 and 1 ≤ 2Ω_Λ/Ω_m ≤ 15.625)
with E² positive at the thirty z values of Table 4, at which the χ² `chiSqOL` is below 14.975 and
χ² + 3 ln N is below 25.705 for every N with 0 < N ≤ 35. -/
theorem oL_bic_exceeds : ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧
    2 * ΩΛ ≤ 15.625 * Ωm ∧ (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧
    chiSqOL H0 Ωm ΩΛ < 14.975 ∧
    ∀ N : ℝ, 0 < N → N ≤ 35 → chiSqOL H0 Ωm ΩΛ + 3 * Real.log N < 25.705 := by
  have hchi : chiSqOL 72.2865 0.43617 0.98144 < 14.975 := by
    unfold chiSqOL
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => term_bound i
    have hU : (∑ i, Checked.Data.Moresco16Certs.cU i) + (72.2865 - 73) ^ 2 / 2.4 ^ 2 < (14.975 : ℝ) := by
      simp only [Checked.Data.Moresco16Certs.cU, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      norm_num
    linarith
  refine ⟨72.2865, 0.43617, 0.98144, by norm_num, by norm_num, by norm_num, by norm_num,
    fun i => by fin_cases i <;> norm_num [e2OL, m16Table], hchi, fun N hN hN35 => ?_⟩
  have hl : Real.log N ≤ Real.log 35 := Real.log_le_log hN hN35
  have := log35_lt
  linarith

/-- There are a, b at which the χ² of the straight line a + b z against H/(1+z) is below 27.972
and χ² + 2 ln N is below 35.285 for every N with 0 < N ≤ 35. -/
theorem line_bic_exceeds : ∃ a b : ℝ, chiSqLine a b < 27.972 ∧
    ∀ N : ℝ, 0 < N → N ≤ 35 → chiSqLine a b + 2 * Real.log N < 35.285 := by
  have hl : chiSqLine 67.13281 (-4.58592) < 27.972 := by
    unfold chiSqLine m16Table
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num
  refine ⟨67.13281, -4.58592, hl, fun N hN hN35 => ?_⟩
  have h := Real.log_le_log hN hN35
  have := log35_lt
  linarith

end Checked.Data.Moresco16
