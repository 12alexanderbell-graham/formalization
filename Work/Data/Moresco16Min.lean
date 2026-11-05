import Mathlib
import Work.Data.Moresco16
import Work.Data.Moresco16MinCover

/-!
# The minimum of the open-ΛCDM χ² of Moresco et al. 2016, certified (THE RESULT part 2)

**Question** (run 2026-11-05T0628Z). Moresco et al. 2016 (arXiv:1601.01701v2) fit the thirty
cosmic-chronometer H(z) values of their Table 4 with the open ΛCDM law (Eq. 5.1) and a Gaussian
prior H₀ = 73 ± 2.4, and print model-comparison numbers (Table 5) built on −2 ln L_max, but not
−2 ln L_max itself. What is the smallest χ² that any parameter values give, to three decimals,
proved over the whole parameter region rather than found by a minimiser?

**What is stated here** (frozen before proof, annex 40.1; definitions `m16Table`, `e2OL`,
`chiSqOL` of `Work.Data.Moresco16`, unchanged):
1. `chiSqOL_ge`: for every H₀ and every (Ω_m, Ω_Λ) with Ω_m ≤ 1, Ω_Λ ≥ 0 and E² ≥ 0 at all
   thirty redshifts (so that the law H₀√E² is real), χ² ≥ 14.9665. The region contains the
   paper's prior region (0 ≤ Ω_m ≤ 1, 0 ≤ z_t ≤ 1.5 with (1 + z_t)³ = 2Ω_Λ/Ω_m).
2. `chiSqOL_lt`: there is a point of the paper's prior region, with E² > 0 at all thirty
   redshifts, where χ² < 14.9675.
3. `chiSqOL_glb_prior`: the greatest lower bound of χ² over the paper's prior region exists and
   lies within 0.0005 of 14.967; `chiSqOL_glb_wide`: the same over the wider region of 1.
4. `table5_oL_aicc_unattainable`: for every N with 4 < N ≤ 31 and every point of the region of 1,
   χ² + 2k + 2k(k + 1)/(N − k − 1) with k = 3 (Eq. 5.4 with −2 ln L = χ²) exceeds the printed
   oΛCDM AICc 21.41 by more than 0.005: no parameter values give the printed number.

**Proof** (run 2026-11-05T0628Z): for fixed (Ω_m, Ω_Λ) the χ² is a quadratic in H₀; tangent
bounds of each √E² and convexity reduce every box of (Ω_m, Ω_Λ) to four exact rational
inequalities, decided by kernel evaluation over ℚ (`Moresco16MinTools.box_boundQ`). The region
lies in [−1, 1] × [0, 4] (E²(1.965) ≥ 0 with Ω_m ≤ 1, Ω_Λ ≥ 0); 905 boxes cover it
(`Moresco16MinCerts0`–`3`, `Moresco16MinCover`; generator `runs/2026-11-05T0628Z/scripts/
gen_min.py`, `emit_min.py`). The upper bound reuses the point certificate of run 0428Z.

**Referee corrections** (`runs/2026-11-05T0628Z/referee_min.md`, STANDS-WITH-CORRECTIONS; added
after the freeze, statements unchanged). The value 14.967 includes the H₀ prior term; the data
part alone at the minimiser is 14.879. Wei, Melia & Wu 2017 (arXiv:1612.08491, Table 1) fit the
same thirty points without the H₀ prior (AIC 20.46, BIC 24.66, i.e. χ² ≈ 14.46; reproduced by the
referee from this table). Claim 4 holds under its premises: Eq. 5.4, k = 3 and −2 ln L_max equal
to this χ² including the prior term. If the column headed AICc holds plain AIC (Eq. 5.3), or if
L_max is the likelihood of the thirty data points without the prior, 21.41 is attainable; the
second reading still does not reproduce the printed BIC. Hypotheses Ω_m ≤ 1 and Ω_Λ ≥ 0 of claim 1
are used by the proof (they bound the region) but, per the referee's float search, not needed for
the bound to hold. The minimum itself (with prior) was not found in print; the JCAP version and
any corrigendum were not reachable.
-/

namespace Work.Data.Moresco16Min
open Work.Data.Moresco16

/-- For every H₀ and every Ω_m ≤ 1, Ω_Λ ≥ 0 at which E² is nonnegative at all thirty redshifts of
Table 4, the open ΛCDM χ² (with the H₀ prior term) is at least 14.9665. -/
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

/-- There are H₀, Ω_m, Ω_Λ in the paper's prior region (0 ≤ Ω_m ≤ 1 and 1 ≤ 2Ω_Λ/Ω_m ≤ 15.625,
i.e. 0 ≤ z_t ≤ 1.5) with E² positive at all thirty redshifts of Table 4, at which the open ΛCDM
χ² is below 14.9675. -/
theorem chiSqOL_lt : ∃ H0 Ωm ΩΛ : ℝ, 0 ≤ Ωm ∧ Ωm ≤ 1 ∧ Ωm ≤ 2 * ΩΛ ∧
    2 * ΩΛ ≤ 15.625 * Ωm ∧ (∀ i, 0 < e2OL Ωm ΩΛ (m16Table i).1) ∧
    chiSqOL H0 Ωm ΩΛ < 14.9675 := by
  have hchi : chiSqOL 72.2865 0.43617 0.98144 < 14.9675 := by
    unfold chiSqOL
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => term_bound i
    have hU : (∑ i, Work.Data.Moresco16Certs.cU i) + (72.2865 - 73) ^ 2 / 2.4 ^ 2 <
        (14.9675 : ℝ) := by
      simp only [Work.Data.Moresco16Certs.cU, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      norm_num
    linarith
  exact ⟨72.2865, 0.43617, 0.98144, by norm_num, by norm_num, by norm_num, by norm_num,
    fun i => by fin_cases i <;> norm_num [e2OL, m16Table], hchi⟩

/-- The greatest lower bound of the open ΛCDM χ² over the paper's prior region (every H₀,
0 ≤ Ω_m ≤ 1, Ω_m ≤ 2Ω_Λ ≤ 15.625 Ω_m, E² positive at all thirty redshifts) exists and is
within 0.0005 of 14.967. -/
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

/-- The greatest lower bound of the open ΛCDM χ² over every H₀ and every Ω_m ≤ 1, Ω_Λ ≥ 0 with E²
nonnegative at all thirty redshifts exists and is within 0.0005 of 14.967. -/
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

/-- Table 5, oΛCDM row: for every N with 4 < N ≤ 31 and every H₀, Ω_m ≤ 1, Ω_Λ ≥ 0 with E²
nonnegative at all thirty redshifts, the AICc of Eq. 5.4 computed with −2 ln L = χ² and k = 3
exceeds the printed 21.41 by more than 0.005. -/
theorem table5_oL_aicc_unattainable (N H0 Ωm ΩΛ : ℝ) (hN : 4 < N) (hN31 : N ≤ 31)
    (hm : Ωm ≤ 1) (hl : 0 ≤ ΩΛ) (hy : ∀ i, 0 ≤ e2OL Ωm ΩΛ (m16Table i).1) :
    21.41 + 0.005 < chiSqOL H0 Ωm ΩΛ + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) := by
  have hc := chiSqOL_ge H0 Ωm ΩΛ hm hl hy
  have hq : (24 : ℝ) / 27 ≤ 2 * 3 * (3 + 1) / (N - 3 - 1) := by
    rw [show (2 : ℝ) * 3 * (3 + 1) = 24 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  norm_num at hq hc ⊢
  linarith

end Work.Data.Moresco16Min

#print axioms Work.Data.Moresco16Min.chiSqOL_ge
#print axioms Work.Data.Moresco16Min.chiSqOL_lt
#print axioms Work.Data.Moresco16Min.chiSqOL_glb_prior
#print axioms Work.Data.Moresco16Min.chiSqOL_glb_wide
#print axioms Work.Data.Moresco16Min.table5_oL_aicc_unattainable
