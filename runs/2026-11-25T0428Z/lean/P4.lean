namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

theorem six_sqrt7 : 6 * Real.sqrt 7 ≤ 16 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  nlinarith [Real.sqrt_nonneg 7]

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem sqrtN_le {a t : ℝ} (ha : a ∈ Ici s0) (hat : a ≤ t) :
    Real.sqrt (Nw (U t - 1) (V t - 2)) ≤ Real.sqrt (Nw (U a - 1) (V a - 2)) :=
  Real.sqrt_le_sqrt (N_le_of S ha hat)

theorem logN_deriv {t : ℝ} (ht : t ∈ Ici s0) :
    HasDerivAt (fun t => Real.log (Nw (U t - 1) (V t - 2)))
      (Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2)) t :=
  (S.dN ht).log (S.N_pos ht).ne'

theorem logN_cont {a b : ℝ} (ha : a ∈ Ici s0) :
    ContinuousOn (fun t => Real.log (Nw (U t - 1) (V t - 2))) (Icc a b) := by
  intro t ht
  have ht' : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1)
  exact (logN_deriv S ht').continuousAt.continuousWithinAt

theorem log_cont {a b : ℝ} (ha : a ∈ Ici s0) : ContinuousOn Real.log (Icc a b) := by
  intro t ht
  have ht' : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1)
  exact (Real.continuousAt_log (S.tpos ht').ne').continuousWithinAt

/-- Bounds on one segment between consecutive zeros of `y`: the angle advances by pi, which bounds the
advance of log t, and log Nw advances at rate −1 up to `36 √Nw`. -/
theorem seg_bounds {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hya : V a = 2)
    (hyb : V b = 2) (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) :
    (Real.sqrt 7 / 2 - 16 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ≤ Real.pi ∧
    Real.pi ≤ (Real.sqrt 7 / 2 + 16 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ∧
    -(1 + 36 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ≤
      Real.log (Nw (U b - 1) (V b - 2)) - Real.log (Nw (U a - 1) (V a - 2)) ∧
    Real.log (Nw (U b - 1) (V b - 2)) - Real.log (Nw (U a - 1) (V a - 2)) ≤
      -(1 - 36 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) := by
  set ε := Real.sqrt (Nw (U a - 1) (V a - 2)) with hε
  have hIcc : ∀ t ∈ Icc a b, t ∈ Ici s0 := fun t ht => mem_Ici.2 (le_trans ha ht.1)
  have hIoo : ∀ t ∈ Ioo a b, t ∈ Ici s0 := fun t ht => hIcc t (Ioo_subset_Icc_self ht)
  have th_c : ContinuousOn (th σ U V) (Icc a b) := (th_cont S).mono (fun t ht => hIcc t ht)
  have lc := log_cont S (b := b) ha
  have lN := logN_cont S (b := b) ha
  have tha := th_left S hσ ha hab hya hsg
  have thb := th_right S hσ ha hab hyb hsg
  have s7 := six_sqrt7
  -- pointwise facts inside
  have inside : ∀ t ∈ Ioo a b, 0 < t ∧ 0 < Nw (U t - 1) (V t - 2) ∧
      Real.sqrt (Nw (U t - 1) (V t - 2)) ≤ ε ∧
      |Lq (U t - 1) (V t - 2) - Nw (U t - 1) (V t - 2) / 4| ≤
        3 * Nw (U t - 1) (V t - 2) * Real.sqrt (Nw (U t - 1) (V t - 2)) ∧
      |Dq (U t - 1) (V t - 2) + Nw (U t - 1) (V t - 2)| ≤
        36 * Nw (U t - 1) (V t - 2) * Real.sqrt (Nw (U t - 1) (V t - 2)) := fun t ht =>
    ⟨S.tpos (hIoo t ht), S.N_pos (hIoo t ht), sqrtN_le S ha ht.1.le, Lq_err _ _, Dq_err _ _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := le_of_deriv (G := fun t => th σ U V t - (Real.sqrt 7 / 2 - 16 * ε) * Real.log t)
      (G' := fun t => 2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t) -
        (Real.sqrt 7 / 2 - 16 * ε) * t⁻¹) hab.le (th_c.sub (continuousOn_const.mul lc))
      (fun t ht => (th_deriv S hσ (hIoo t ht) (hsg t ht)).sub
        ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
      (fun t ht => by
        obtain ⟨tp, Np, sl, hL, -⟩ := inside t ht
        have hL1 := (abs_le.1 hL).1
        have e : 2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t) -
            (Real.sqrt 7 / 2 - 16 * ε) * t⁻¹ =
            (2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) - (Real.sqrt 7 / 2 - 16 * ε) * Nw (U t - 1) (V t - 2)) /
              (Nw (U t - 1) (V t - 2) * t) := by field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        have s7p : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
        have hr : 0 ≤ Real.sqrt (Nw (U t - 1) (V t - 2)) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 7),
          mul_le_mul_of_nonneg_left sl Np.le, mul_nonneg Np.le hr,
          mul_le_mul_of_nonneg_right s7 (mul_nonneg Np.le hr)])
    simp only [tha, thb] at this
    linarith
  · have := le_of_deriv (G := fun t => (Real.sqrt 7 / 2 + 16 * ε) * Real.log t - th σ U V t)
      (G' := fun t => (Real.sqrt 7 / 2 + 16 * ε) * t⁻¹ -
        2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t)) hab.le
      ((continuousOn_const.mul lc).sub th_c)
      (fun t ht => ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _).sub
        (th_deriv S hσ (hIoo t ht) (hsg t ht)))
      (fun t ht => by
        obtain ⟨tp, Np, sl, hL, -⟩ := inside t ht
        have hL1 := (abs_le.1 hL).2
        have e : (Real.sqrt 7 / 2 + 16 * ε) * t⁻¹ -
            2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t) =
            ((Real.sqrt 7 / 2 + 16 * ε) * Nw (U t - 1) (V t - 2) - 2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2)) /
              (Nw (U t - 1) (V t - 2) * t) := by field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        have s7p : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
        have hr : 0 ≤ Real.sqrt (Nw (U t - 1) (V t - 2)) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 7),
          mul_le_mul_of_nonneg_left sl Np.le, mul_nonneg Np.le hr,
          mul_le_mul_of_nonneg_right s7 (mul_nonneg Np.le hr)])
    simp only [tha, thb] at this
    linarith
  · have := le_of_deriv (G := fun t => Real.log (Nw (U t - 1) (V t - 2)) + (1 + 36 * ε) * Real.log t)
      (G' := fun t => Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2) + (1 + 36 * ε) * t⁻¹) hab.le
      (lN.add (continuousOn_const.mul lc))
      (fun t ht => (logN_deriv S (hIoo t ht)).add ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
      (fun t ht => by
        obtain ⟨tp, Np, sl, -, hD⟩ := inside t ht
        have hD1 := (abs_le.1 hD).1
        have e : Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2) + (1 + 36 * ε) * t⁻¹ =
            (Dq (U t - 1) (V t - 2) + (1 + 36 * ε) * Nw (U t - 1) (V t - 2)) / (Nw (U t - 1) (V t - 2) * t) := by
          field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left sl Np.le])
    linarith
  · have := le_of_deriv (G := fun t => -Real.log (Nw (U t - 1) (V t - 2)) - (1 - 36 * ε) * Real.log t)
      (G' := fun t => -(Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2)) - (1 - 36 * ε) * t⁻¹) hab.le
      (lN.neg.sub (continuousOn_const.mul lc))
      (fun t ht => (logN_deriv S (hIoo t ht)).neg.sub ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
      (fun t ht => by
        obtain ⟨tp, Np, sl, -, hD⟩ := inside t ht
        have hD1 := (abs_le.1 hD).2
        have e : -(Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2)) - (1 - 36 * ε) * t⁻¹ =
            (-Dq (U t - 1) (V t - 2) - (1 - 36 * ε) * Nw (U t - 1) (V t - 2)) / (Nw (U t - 1) (V t - 2) * t) := by
          field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left sl Np.le])
    linarith

end Sys
end GTR
