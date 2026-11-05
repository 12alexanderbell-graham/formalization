import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Checked.Data.Moresco16
import Checked.Data.Moresco16MinCover

/-!
# The minimum of the open-universe χ² of Moresco et al. 2016, certified (THE RESULT part 2)

Promoted from `Work/Data/Moresco16Min.lean` (run 2026-11-05T0628Z: freeze, proof, blind restatement
closed, referee) in run 2026-11-05T1028Z: statements and proofs unchanged, specific Mathlib imports,
prose rewritten for the prose rules (the Work module doc keeps the full discussion).

**Question.** Moresco et al. fit the thirty measurements of their Table 4 by the open-universe law
with a Gaussian prior on H₀ and print model-comparison numbers built on −2 ln L_max, but not
−2 ln L_max itself. What is the smallest χ² that any parameter values give, proved over the whole
parameter region rather than found by a minimiser?

**What is stated here** (frozen before proof; definitions of `Checked.Data.Moresco16`):
1. `chiSqOL_ge`: for every H₀ and every (Ω_m, Ω_Λ) with Ω_m ≤ 1, Ω_Λ ≥ 0 and E² ≥ 0 at all thirty
   z values, χ² ≥ 14.9665.
2. `chiSqOL_lt`: there is a point of the paper's prior region, with E² > 0 at all thirty z values,
   where χ² < 14.9675.
3. `chiSqOL_glb_prior`, `chiSqOL_glb_wide`: the greatest lower bound of χ² over the prior region,
   and over the region of 1, exists and lies within 0.0005 of 14.967.
4. `table5_oL_aicc_unattainable`: for every real N with 4 < N ≤ 31 and every point of the region of
   1, χ² + 2k + 2k(k + 1)/(N − k − 1) with k = 3 exceeds the printed oLCDM AICc 21.41 by more than
   0.005.

**Proof.** For fixed (Ω_m, Ω_Λ) the χ² is a quadratic in H₀; tangent bounds of each √E² and convexity
reduce every box of (Ω_m, Ω_Λ) to four exact rational inequalities, decided by kernel evaluation
over ℚ (`Checked.Data.Moresco16MinTools.box_boundQ`); the boxes of `Moresco16MinCerts0`–`3`, joined
by `Moresco16MinCover`, cover the region. The upper bound reuses the point certificate of
`Checked.Data.Moresco16Certs`.

**Referee corrections** (`runs/2026-11-05T0628Z/referee_min.md`, STANDS-WITH-CORRECTIONS). The
minimum includes the H₀ prior term. Claim 4 holds under its premises (the corrected criterion with
k = 3 and −2 ln L_max equal to this χ² including the prior term); if the column headed AICc holds the
plain AIC, or if L_max is the likelihood of the thirty data points without the prior, 21.41 is
attainable (`Work/Data/Moresco16MinNearMiss.lean` proves the first). The minimum itself was not
found in print.
-/

namespace Checked.Data.Moresco16Min
open Checked.Data.Moresco16

/-- For every H0, every Ωm ≤ 1 and every ΩΛ ≥ 0 at which E² is nonnegative at the thirty z values
of Table 4, the χ² `chiSqOL` (with the H₀ prior term) is at least 14.9665. -/
theorem chiSqOL_ge (H0 Ωm ΩΛ : ℝ) (hm : Ωm ≤ 1) (hl : 0 ≤ ΩΛ)
    (hy : ∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) :
    14.9665 ≤ chiSqOL H0 Ωm ΩΛ := by
  have hb := hy 29
  norm_num [e2OL, m16Table] at hb
  have hm0 : -1 ≤ Ωm := by nlinarith
  have hl4 : ΩΛ ≤ 4 := by nlinarith
  have h := n H0 Ωm ΩΛ (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith) hy
  norm_num at h ⊢
  linarith

/-- There are H₀, Ω_m, Ω_Λ in the paper's prior region (0 ≤ Ω_m ≤ 1 and 1 ≤ 2Ω_Λ/Ω_m ≤ 15.625)
with E² positive at the thirty z values of Table 4, at which the χ² `chiSqOL` is below 14.9675. -/
theorem chiSqOL_lt : ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧
    2 * ΩΛ ≤ 15.625 * Ωm ∧ (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧
    chiSqOL H0 Ωm ΩΛ < 14.9675 := by
  have hchi : chiSqOL 72.2865 0.43617 0.98144 < 14.9675 := by
    unfold chiSqOL
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => term_bound i
    have hU : (∑ i, Checked.Data.Moresco16Certs.cU i) + (72.2865 - 73) ^ 2 / 2.4 ^ 2 <
        (14.9675 : ℝ) := by
      simp only [Checked.Data.Moresco16Certs.cU, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      norm_num
    linarith
  exact ⟨72.2865, 0.43617, 0.98144, by norm_num, by norm_num, by norm_num, by norm_num,
    fun i => by fin_cases i <;> norm_num [e2OL, m16Table], hchi⟩

/-- The greatest lower bound of the χ² `chiSqOL` over the paper's prior region (the points
with 0 ≤ Ωm ≤ 1, Ωm ≤ 2ΩΛ ≤ 15.625 Ωm and E² positive at the thirty z values of Table 4, H₀
free) exists and is within 0.0005 of 14.967. -/
theorem chiSqOL_glb_prior : ∃ m : ℝ,
    IsGLB {x | ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧ 2 * ΩΛ ≤ 15.625 * Ωm ∧
      (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} m ∧
    |m - 14.967| ≤ 0.0005 := by
  obtain ⟨H1, m1, l1, a1, a2, a3, a4, a5, a6⟩ := chiSqOL_lt
  set S := {x | ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧ 2 * ΩΛ ≤ 15.625 * Ωm ∧
      (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} with hS
  have hmem : chiSqOL H1 m1 l1 ∈ S := ⟨H1, m1, l1, a1, a2, a3, a4, a5, rfl⟩
  have hlow : ∀ x ∈ S, 14.9665 ≤ x := by
    rintro x ⟨H0, Ωm, ΩΛ, b1, b2, b3, b4, b5, rfl⟩
    exact chiSqOL_ge H0 Ωm ΩΛ b2 (by linarith) fun i => (b5 i).le
  have hne : S.Nonempty := ⟨_, hmem⟩
  have hbdd : BddBelow S := ⟨14.9665, hlow⟩
  refine ⟨sInf S, isGLB_csInf hne hbdd, ?_⟩
  have h1 : 14.9665 ≤ sInf S := le_csInf hne hlow
  have h2 : sInf S ≤ chiSqOL H1 m1 l1 := csInf_le hbdd hmem
  rw [abs_le]; constructor <;> linarith

/-- The greatest lower bound of the χ² `chiSqOL` over the points (H₀, Ωm, ΩΛ) with Ωm ≤ 1,
ΩΛ ≥ 0 and E² nonnegative at the thirty z values of Table 4 exists and is within 0.0005 of 14.967. -/
theorem chiSqOL_glb_wide : ∃ m : ℝ,
    IsGLB {x | ∃ H0 Ωm ΩΛ : ℝ, Ωm ≤ 1 ∧ 0 ≤ ΩΛ ∧
      (∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} m ∧
    |m - 14.967| ≤ 0.0005 := by
  obtain ⟨H1, m1, l1, a1, a2, a3, a4, a5, a6⟩ := chiSqOL_lt
  set S := {x | ∃ H0 Ωm ΩΛ : ℝ, Ωm ≤ 1 ∧ 0 ≤ ΩΛ ∧
      (∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) ∧ x = chiSqOL H0 Ωm ΩΛ} with hS
  have hmem : chiSqOL H1 m1 l1 ∈ S :=
    ⟨H1, m1, l1, a2, by linarith, fun i => (a5 i).le, rfl⟩
  have hlow : ∀ x ∈ S, 14.9665 ≤ x := by
    rintro x ⟨H0, Ωm, ΩΛ, b1, b2, b3, rfl⟩
    exact chiSqOL_ge H0 Ωm ΩΛ b1 b2 b3
  have hne : S.Nonempty := ⟨_, hmem⟩
  have hbdd : BddBelow S := ⟨14.9665, hlow⟩
  refine ⟨sInf S, isGLB_csInf hne hbdd, ?_⟩
  have h1 : 14.9665 ≤ sInf S := le_csInf hne hlow
  have h2 : sInf S ≤ chiSqOL H1 m1 l1 := csInf_le hbdd hmem
  rw [abs_le]; constructor <;> linarith

/-- Table 5, row oLCDM: for every N with 4 < N ≤ 31, every H0, every Ωm ≤ 1 and every ΩΛ ≥ 0
with E² nonnegative at the thirty z values of Table 4, the corrected Akaike criterion
χ² + 2k + 2k(k + 1)/(N − k − 1) with k = 3 exceeds the printed 21.41 by more than 0.005. -/
theorem table5_oL_aicc_unattainable (N H0 Ωm ΩΛ : ℝ) (hN : 4 < N) (hN31 : N ≤ 31)
    (hm : Ωm ≤ 1) (hl : 0 ≤ ΩΛ) (hy : ∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) :
    21.41 + 0.005 < chiSqOL H0 Ωm ΩΛ + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) := by
  have hc := chiSqOL_ge H0 Ωm ΩΛ hm hl hy
  have hq : (24 : ℝ) / 27 ≤ 2 * 3 * (3 + 1) / (N - 3 - 1) := by
    rw [show (2 : ℝ) * 3 * (3 + 1) = 24 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  norm_num at hq hc ⊢
  linarith

end Checked.Data.Moresco16Min
