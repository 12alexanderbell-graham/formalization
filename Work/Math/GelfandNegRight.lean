import Checked.Math.GExistsRight

/-! Gelfand problem with a negative parameter, right piece: existence away from the centre by
Picard–Lindelöf for (w, s² φ) with the field φ' = −(2/s)φ + e^{min w M} (sign-flipped, clamped copy of
`Checked.Math.GExistsRight.exists_right`). -/

namespace Work.Math.GelfandNegRight
open Set Checked.Math.GExistsRight

/-- The clamped field in (w, q), positive exponential clamped at `M`. -/
noncomputable def gnF (M Q : ℝ) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cl Q p.2 / t ^ 2, t ^ 2 * Real.exp (min p.1 M))

theorem gn_lipF {M Q T t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) T) :
    LipschitzWith (Real.toNNReal (4 + T ^ 2 * Real.exp M)) (gnF M Q t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have heM := Real.exp_pos M
  have hK : (0 : ℝ) ≤ 4 + T ^ 2 * Real.exp M := by positivity
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ hK]
  simp only [gnF, Prod.dist_eq, Real.dist_eq]
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hm0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := (abs_nonneg _).trans hd1
  have ht2 : 1 / 4 ≤ t ^ 2 := by nlinarith [ht.1]
  have htT : t ^ 2 ≤ T ^ 2 := by
    have := ht.2; nlinarith [ht.1]
  refine max_le ?_ ?_
  · rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    have := cl_sub Q p.2 q.2
    have a := mul_le_mul_of_nonneg_right ht2 hm0
    have b : 0 ≤ T ^ 2 * Real.exp M * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by positivity
    have h4 : |p.2 - q.2| ≤ (4 + T ^ 2 * Real.exp M) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by
      have e : (4 + T ^ 2 * Real.exp M) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 =
          4 * (t ^ 2 * max |p.1 - q.1| |p.2 - q.2|) +
            T ^ 2 * Real.exp M * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by
        ring
      rw [e]; linarith
    linarith
  · have e : t ^ 2 * Real.exp (min p.1 M) - t ^ 2 * Real.exp (min q.1 M) =
        t ^ 2 * (Real.exp (min p.1 M) - Real.exp (min q.1 M)) := by ring
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have h1 := exp_sub_le_of_le (min_le_right p.1 M) (min_le_right q.1 M)
    have h2 : |min p.1 M - min q.1 M| ≤ |p.1 - q.1| := abs_min_sub_min_le_max _ _ _ _ |>.trans
      (max_le le_rfl (by simp))
    have h3 : |Real.exp (min p.1 M) - Real.exp (min q.1 M)| ≤
        Real.exp M * max |p.1 - q.1| |p.2 - q.2| :=
      h1.trans (mul_le_mul_of_nonneg_left (h2.trans hd1) heM.le)
    calc t ^ 2 * |Real.exp (min p.1 M) - Real.exp (min q.1 M)|
        ≤ T ^ 2 * (Real.exp M * max |p.1 - q.1| |p.2 - q.2|) :=
          mul_le_mul htT h3 (abs_nonneg _) (sq_nonneg _)
      _ ≤ (4 + T ^ 2 * Real.exp M) * max |p.1 - q.1| |p.2 - q.2| := by nlinarith

theorem gn_normF {M Q T t : ℝ} (hQ : 0 ≤ Q) (ht : t ∈ Icc (1 / 2 : ℝ) T) (p : ℝ × ℝ) :
    ‖gnF M Q t p‖ ≤ 4 * Q + T ^ 2 * Real.exp M := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht2 : 1 / 4 ≤ t ^ 2 := by nlinarith [ht.1]
  have htT : t ^ 2 ≤ T ^ 2 := by
    have := ht.2; nlinarith [ht.1]
  simp only [gnF, Prod.norm_def, Real.norm_eq_abs]
  have hc := abs_cl_le hQ p.2
  have heM := Real.exp_pos M
  refine max_le ?_ ?_
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg T, abs_nonneg (cl Q p.2), mul_nonneg (sq_nonneg T) heM.le]
  · rw [abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_pos (Real.exp_pos _)]
    have : Real.exp (min p.1 M) ≤ Real.exp M := Real.exp_le_exp.2 (min_le_right _ _)
    have h5 := Real.exp_pos (min p.1 M)
    nlinarith [mul_le_mul htT this h5.le (sq_nonneg T)]

theorem gn_contF {M Q T : ℝ} (x : ℝ × ℝ) :
    ContinuousOn (fun t => gnF M Q t x) (Icc (1 / 2 : ℝ) T) := by
  unfold gnF
  refine ContinuousOn.prodMk ?_ ?_
  · exact continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity
  · exact ((continuousOn_id.pow 2).mul continuousOn_const)

theorem exists_right (T M w₀ φ₀ : ℝ) (hT : 1 / 2 ≤ T) (hφ₀ : 0 ≤ φ₀) (hφ₀' : φ₀ ≤ 1) :
    ∃ w φ : ℝ → ℝ, w (1 / 2) = w₀ ∧ φ (1 / 2) = φ₀ ∧
      ∀ t ∈ Icc (1 / 2 : ℝ) T, HasDerivWithinAt w (φ t) (Icc (1 / 2) T) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) + Real.exp (min (w t) M)) (Icc (1 / 2) T) t := by
  have hT0 : 0 < T := by linarith
  have heM := Real.exp_pos M
  set Q : ℝ := T ^ 3 * Real.exp M + 1 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set L : ℝ := 4 * Q + T ^ 2 * Real.exp M with hL
  have hL0 : 0 ≤ L := by positivity
  set q₀ : ℝ := φ₀ / 4 with hq₀
  have hPL : IsPicardLindelof (gnF M Q) (tmin := 1 / 2) (tmax := T)
      ⟨1 / 2, le_rfl, hT⟩ (w₀, q₀) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (4 + T ^ 2 * Real.exp M)) :=
    { lipschitzOnWith := fun t ht => (gn_lipF ht).lipschitzOnWith
      continuousOn := fun x _ => gn_contF x
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact gn_normF hQ0 ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, NNReal.coe_zero, sub_zero,
          Real.coe_toNNReal _ (by positivity)]
        simp only
        rw [sub_self, max_eq_left (by linarith)]
        nlinarith }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  simp only at h0
  set w : ℝ → ℝ := fun t => (α t).1 with hw
  set q : ℝ → ℝ := fun t => (α t).2 with hq
  have hw0 : w (1 / 2) = w₀ := by simp only [hw, h0]
  have hq0 : q (1 / 2) = q₀ := by simp only [hq, h0]
  have dw : ∀ t ∈ Icc (1 / 2 : ℝ) T, HasDerivWithinAt w (cl Q (q t) / t ^ 2) (Icc (1 / 2) T) t :=
    fun t ht => by have := fst_derivW (hα t ht); simpa [gnF] using this
  have dq : ∀ t ∈ Icc (1 / 2 : ℝ) T,
      HasDerivWithinAt q (t ^ 2 * Real.exp (min (w t) M)) (Icc (1 / 2) T) t :=
    fun t ht => by have := snd_derivW (hα t ht); simpa [gnF] using this
  have cq : ContinuousOn q (Icc (1 / 2) T) := fun t ht => (dq t ht).continuousWithinAt
  -- q increases
  have qmono : MonotoneOn q (Icc (1 / 2) T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) cq
      (fun t ht => ((dq t (interior_subset ht)).mono interior_subset))
    intro t _
    have := Real.exp_pos (min (w t) M)
    positivity
  -- q − T² e^M t decreases
  have qanti : AntitoneOn (fun t => q t - T ^ 2 * Real.exp M * t) (Icc (1 / 2) T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (cq.sub (continuousOn_const.mul continuousOn_id))
      (fun t ht => (((dq t (interior_subset ht)).sub
        ((hasDerivAt_id t).const_mul (T ^ 2 * Real.exp M)).hasDerivWithinAt).mono interior_subset))
    intro t ht
    rw [interior_Icc] at ht
    have h1 : Real.exp (min (w t) M) ≤ Real.exp M := Real.exp_le_exp.2 (min_le_right _ _)
    have h2 : t ^ 2 ≤ T ^ 2 := by nlinarith [ht.1, ht.2]
    have h3 := Real.exp_pos (min (w t) M)
    simp only [mul_one]
    nlinarith [mul_le_mul h2 h1 h3.le (sq_nonneg T)]
  have hm : (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) T := ⟨le_rfl, hT⟩
  have qge : ∀ t ∈ Icc (1 / 2 : ℝ) T, q₀ ≤ q t := fun t ht => by
    rw [← hq0]; exact qmono hm ht ht.1
  have qle : ∀ t ∈ Icc (1 / 2 : ℝ) T, q t ≤ q₀ + T ^ 3 * Real.exp M := fun t ht => by
    have h := qanti hm ht ht.1
    simp only [hq0] at h
    have : T ^ 2 * Real.exp M * t ≤ T ^ 3 * Real.exp M := by
      have := ht.2
      have e : T ^ 3 * Real.exp M = T ^ 2 * Real.exp M * T := by ring
      rw [e]; exact mul_le_mul_of_nonneg_left this (by positivity)
    have : 0 ≤ T ^ 2 * Real.exp M * (1 / 2) := by positivity
    linarith
  have qin : ∀ t ∈ Icc (1 / 2 : ℝ) T, |q t| ≤ Q := fun t ht => by
    have h1 := qle t ht
    have h2 := qge t ht
    have h3 : q₀ ≤ 1 / 4 := by rw [hq₀]; linarith
    have h4 : 0 ≤ q₀ := by rw [hq₀]; linarith
    rw [abs_le]; constructor <;> linarith
  have hqcl : ∀ t ∈ Icc (1 / 2 : ℝ) T, cl Q (q t) = q t := fun t ht => cl_of_abs_le (qin t ht)
  refine ⟨w, fun t => q t / t ^ 2, hw0, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [hq0, hq₀]; norm_num; ring
  · have := dw t ht
    rwa [hqcl t ht] at this
  · have ht0 : t ≠ 0 := by have := ht.1; positivity
    have h := (dq t ht).div ((hasDerivAt_pow 2 t).hasDerivWithinAt) (pow_ne_zero 2 ht0)
    convert h using 1
    field_simp
    ring

end Work.Math.GelfandNegRight
