import Mathlib
import Readings.logbm
import ComparatorChallenges.LogBrunnMinkowski

/-! # Target O, family O47 (logarithmic Brunn–Minkowski): closures (run 2026-11-27T1428Z).
Frozen statement `main` (volumes in `ℝ≥0∞`), taken with `type_of%`, never retyped. The readers state volumes as
real numbers (`toReal`); `toReal` hides an infinite volume as `0`, so the closure proves the frozen Wulff body
bounded (inside the ball of radius `R` when `K, L ⊆ ball R`: the support functions are nonnegative by symmetry and
at most `R`), hence of finite volume, before taking `toReal`. Closed: every reader's Theorem 1.1 (3/3), reader A's
finiteness conjunct included. Corollary 1.2 (symmetric `L_p`) has no Lean statement in the family and is not
closed here. -/

namespace TargetO.LogBM

open OAI.LogBrunnMinkowski MeasureTheory Metric
open scoped InnerProductSpace

variable {n : ℕ}

theorem support_nonneg {K : Set (Space n)} (hK : K.Nonempty) (hs : OriginSymmetric K) (u : Space n)
    (hb : BddAbove ((fun x : Space n => ⟪x, u⟫_ℝ) '' K)) : 0 ≤ support K u := by
  obtain ⟨x, hx⟩ := hK
  have h1 : ⟪x, u⟫_ℝ ≤ support K u := le_csSup hb ⟨x, hx, rfl⟩
  have h2 : ⟪-x, u⟫_ℝ ≤ support K u := le_csSup hb ⟨-x, (hs x).1 hx, rfl⟩
  rw [inner_neg_left] at h2
  linarith

theorem support_le {K : Set (Space n)} (hK : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u : Space n)
    (hu : ‖u‖ = 1) : support K u ≤ R := by
  apply csSup_le (hK.image _)
  rintro _ ⟨x, hx, rfl⟩
  calc ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
    _ = ‖x‖ := by rw [hu, mul_one]
    _ ≤ R := hR x hx

theorem bdd_image {K : Set (Space n)} {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R) (u : Space n) (hu : ‖u‖ = 1) :
    BddAbove ((fun x : Space n => ⟪x, u⟫_ℝ) '' K) := by
  refine ⟨R, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  calc ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
    _ = ‖x‖ := by rw [hu, mul_one]
    _ ≤ R := hR x hx

/-- The frozen log-combination of two bounded origin-symmetric bodies lies in a ball, so its volume is finite. -/
theorem logComb_finite {K L : Set (Space n)} (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hsK : OriginSymmetric K) (hsL : OriginSymmetric L) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (logCombination K L t) ≠ ⊤ := by
  obtain ⟨R1, hR1⟩ := hK.1.isBounded.exists_norm_le
  obtain ⟨R2, hR2⟩ := hL.1.isBounded.exists_norm_le
  set R := max (max R1 R2) 0
  have hRK : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => (hR1 x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hRL : ∀ x ∈ L, ‖x‖ ≤ R := fun x hx => (hR2 x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hR0 : 0 ≤ R := le_max_right _ _
  have hKne : K.Nonempty := hK.2.2.mono interior_subset
  have hLne : L.Nonempty := hL.2.2.mono interior_subset
  have hsub : logCombination K L t ⊆ closedBall 0 R := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    by_cases hx0 : x = 0
    · rw [hx0, norm_zero]; exact hR0
    set u : Space n := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hx0
    have hxu : ⟪x, u⟫_ℝ = ‖x‖ := by
      simp only [u, inner_smul_right, real_inner_self_eq_norm_sq]
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
      field_simp
    have h := hx u hu
    rw [hxu] at h
    have a0 := support_nonneg hKne hsK u (bdd_image hRK u hu)
    have b0 := support_nonneg hLne hsL u (bdd_image hRL u hu)
    have a1 := support_le hKne hRK u hu
    have b1 := support_le hLne hRL u hu
    calc ‖x‖ ≤ support K u ^ (1 - t) * support L u ^ t := h
      _ ≤ R ^ (1 - t) * R ^ t := by
          exact mul_le_mul (Real.rpow_le_rpow a0 a1 (by linarith)) (Real.rpow_le_rpow b0 b1 ht0)
            (Real.rpow_nonneg b0 _) (Real.rpow_nonneg hR0 _)
      _ = R := by
          rcases hR0.lt_or_eq with hpos | hzero
          · rw [← Real.rpow_add hpos]; simp
          · rw [← hzero]
            rcases ht0.lt_or_eq with htp | htz
            · rw [Real.zero_rpow (ne_of_gt htp)]; simp
            · rw [← htz]; simp
  exact ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : Space n)) (r := R)).ne (measure_mono hsub)

/-- The frozen inequality in real numbers. -/
theorem frozen_real (H : type_of% @main) (n : ℕ) (hn : 1 ≤ n) (K L : Set (Space n))
    (hK : IsConvexBody K) (hL : IsConvexBody L) (hsK : OriginSymmetric K) (hsL : OriginSymmetric L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (logCombination K L t) ≠ ⊤ ∧
      (volume K).toReal ^ (1 - t) * (volume L).toReal ^ t ≤ (volume (logCombination K L t)).toReal := by
  have hfin := logComb_finite hK hL hsK hsL t ht0 ht1
  refine ⟨hfin, ?_⟩
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin (H n hn K L hK hL hsK hsL t ht0 ht1)

theorem sym_of_neg {K : Set (Space n)} (h : K = -K) : OriginSymmetric K := by
  intro x
  constructor
  · intro hx; rw [h] at hx; simpa using hx
  · intro hx; rw [h]; simpa using hx

theorem wulff_eqA (f : Space n → ℝ) : ReaderA.wulff f = wulff f := by
  ext x; simp [ReaderA.wulff, wulff]

theorem wulff_eqB (f : Space n → ℝ) : ReaderB.wulff f = wulff f := by
  ext x; simp [ReaderB.wulff, wulff]

theorem wulff_eqC (f : Space n → ℝ) : ReaderC.wulff f = wulff f := by
  ext x; simp [ReaderC.wulff, wulff]

theorem A_thm (H : type_of% @main) : type_of% @ReaderA.reading_thm_1_1 := by
  intro n hn K L hK hL hKs hLs t ht0 ht1
  have := frozen_real H n hn K L hK hL (sym_of_neg hKs) (sym_of_neg hLs) t ht0 ht1
  rw [wulff_eqA]; exact this

theorem B_thm (H : type_of% @main) : type_of% @ReaderB.reading_thm_1_1 := by
  intro n hn K L hK hL hKs hLs t ht0 ht1
  have := frozen_real H n hn K L hK hL (sym_of_neg hKs) (sym_of_neg hLs) t ht0 ht1
  rw [wulff_eqB]; exact this.2

theorem C_thm (H : type_of% @main) : type_of% @ReaderC.reading_theorem_1_1 := by
  intro n hn K L hK hL hKs hLs t ht0 ht1
  have := frozen_real H n hn K L hK hL hKs hLs t ht0 ht1
  rw [wulff_eqC]; exact this.2

end TargetO.LogBM

#print axioms TargetO.LogBM.A_thm
#print axioms TargetO.LogBM.B_thm
#print axioms TargetO.LogBM.C_thm
