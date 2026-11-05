import Mathlib
import Work.Data.Moresco16
import Work.Data.Moresco16Blind

/-!
# Moresco et al. 2016 Table 5: the blind restatement, closed

The blind restatement (`Work/Data/Moresco16Blind.lean`, Sonnet, written from the paper alone)
reads the question with natural N ∈ {30, 31}, any tolerance ε ≤ 1/10 (twenty times the rounding
tolerance of the frozen statement), z_t instead of Ω_Λ as parameter (Ω_Λ = Ω_m(1 + z_t)³/2), and
χ² written as ((H − model)/σ)². Each blind statement is proved here with its text unchanged
(namespace `Work.Data.Moresco16Blind`, definitions of the blind file); certificates for (b) by
`runs/2026-11-05T0428Z/scripts/gen_m16.py` with `M16_ZT=0.651 M16_SFX=b`.
-/

namespace Work.Data.Moresco16BlindClosed
open Work.Data.Moresco16Blind Work.Data.Moresco16Certs

/-- (a), closed: in every row of Table 5, for N ∈ {30, 31} and every tolerance ε ≤ 1/10, no
single value of −2 ln L_max reproduces both the printed AICc and the printed BIC. -/
theorem table5_inconsistent (i : Fin 3) (N : ℕ) (hN : N = 30 ∨ N = 31) (ε : ℝ) (hε : ε ≤ 1/10) :
    ¬ ∃ x : ℝ, |AICc x (table5 i).1 N - (table5 i).2.1| ≤ ε ∧
                |BIC x (table5 i).1 N - (table5 i).2.2| ≤ ε := by
  rintro ⟨x, h1, h2⟩
  have hN30 : (30 : ℝ) ≤ N := by rcases hN with h | h <;> subst h <;> norm_num
  have hN31 : (N : ℝ) ≤ 31 := by rcases hN with h | h <;> subst h <;> norm_num
  have hl : Real.log N ≤ Real.log 31 := Real.log_le_log (by linarith) hN31
  have h31 := Work.Data.Moresco16.log31_lt
  have a1 := (abs_le.1 h1).2
  have b1 := (abs_le.1 h2).1
  simp only [AICc, AIC, BIC] at a1 b1
  fin_cases i <;> simp [table5] at a1 b1 <;> norm_num at a1 b1
  · have hq : (24 : ℝ) / 27 ≤ 2 * 3 * (3 + 1) / ((N : ℝ) - 3 - 1) := by
      rw [show (2 : ℝ) * 3 * (3 + 1) = 24 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    norm_num at hq; nlinarith
  · have hq : (40 : ℝ) / 26 ≤ 2 * 4 * (4 + 1) / ((N : ℝ) - 4 - 1) := by
      rw [show (2 : ℝ) * 4 * (4 + 1) = 40 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    norm_num at hq; nlinarith
  · have hq : (12 : ℝ) / 28 ≤ 2 * 2 * (2 + 1) / ((N : ℝ) - 2 - 1) := by
      rw [show (2 : ℝ) * 2 * (2 + 1) = 12 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    norm_num at hq; nlinarith

set_option maxHeartbeats 8000000 in
/-- Each blind χ² term at (72.2865, 0.43617, 0.651) is at most the certificate `cUb i`
(helper). -/
theorem term_bound_b (i : Fin 30) :
    (((table4 i).2.1 - 72.2865 * Real.sqrt (0.43617 * (1 + (table4 i).1) ^ 3 +
        (1 - 0.43617 - 0.43617 * (1 + 0.651) ^ 3 / 2) * (1 + (table4 i).1) ^ 2 +
        0.43617 * (1 + 0.651) ^ 3 / 2)) / (table4 i).2.2) ^ 2 ≤ cUb i := by
  rw [div_pow, show ∀ u v : ℝ, (u - v) ^ 2 = (v - u) ^ 2 from fun u v => by ring]
  apply term_le (s := cSb i) (ε := 1 / 10 ^ 9) (A := cAb i) <;> fin_cases i <;>
    norm_num [cSb, cAb, cUb, table4]

/-- (b), closed: for N ∈ {30, 31} there are H₀, Ω_m ∈ [0, 1], z_t ∈ [0, 1.5] with nonnegative
radicand at all thirty redshifts and oΛCDM BIC below 25.705. -/
theorem oLCDM_bic_below_printed (N : ℕ) (hN : N = 30 ∨ N = 31) :
    ∃ H0 Om zt : ℝ, Om ∈ Set.Icc (0:ℝ) 1 ∧ zt ∈ Set.Icc (0:ℝ) 1.5 ∧ radicandNonneg Om zt ∧
      BIC (chi2OLCDM H0 Om zt) 3 N < 25.71 - 0.005 := by
  have hchi : chi2OLCDM 72.2865 0.43617 0.651 < 14.975 := by
    unfold chi2OLCDM
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => term_bound_b i
    have hU : (∑ i, cUb i) + ((72.2865 - 73) / 2.4) ^ 2 < (14.975 : ℝ) := by
      simp only [cUb, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      norm_num
    linarith
  have hN31 : (N : ℝ) ≤ 31 := by rcases hN with h | h <;> subst h <;> norm_num
  have hN0 : (0 : ℝ) < N := by rcases hN with h | h <;> subst h <;> norm_num
  have hl : Real.log N ≤ Real.log 31 := Real.log_le_log hN0 hN31
  have h31 := Work.Data.Moresco16.log31_lt
  refine ⟨72.2865, 0.43617, 0.651, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    fun i => by fin_cases i <;> norm_num [table4], ?_⟩
  simp only [BIC]
  push_cast
  linarith

/-- (c), closed: for N ∈ {30, 31} there are a, b with linear-fit BIC below 35.285. -/
theorem linear_bic_below_printed (N : ℕ) (hN : N = 30 ∨ N = 31) :
    ∃ a b : ℝ, BIC (chi2Linear a b) 2 N < 35.29 - 0.005 := by
  have hl : chi2Linear 67.13281 (-4.58592) < 27.972 := by
    unfold chi2Linear table4
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    norm_num
  have hN31 : (N : ℝ) ≤ 31 := by rcases hN with h | h <;> subst h <;> norm_num
  have hN0 : (0 : ℝ) < N := by rcases hN with h | h <;> subst h <;> norm_num
  have h := Real.log_le_log hN0 hN31
  have h31 := Work.Data.Moresco16.log31_lt
  refine ⟨67.13281, -4.58592, ?_⟩
  simp only [BIC]
  push_cast
  linarith

end Work.Data.Moresco16BlindClosed

#print axioms Work.Data.Moresco16BlindClosed.table5_inconsistent
#print axioms Work.Data.Moresco16BlindClosed.oLCDM_bic_below_printed
#print axioms Work.Data.Moresco16BlindClosed.linear_bic_below_printed
