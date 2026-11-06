import Mathlib

/-!
# Gelfand problem: existence on [1/2, T] from any start with w₀ ≤ 0, −1 ≤ φ₀ ≤ 0

Picard–Lindelöf (Mathlib) in the variables (w, q), q = t²φ, for the clamped field
f t (w, q) = (cl Q q / t², −(t² e^{min w 0})), Q = T³ + 1, Lipschitz (constant 4 + T²) and
bounded (4Q + T²) for t ∈ [1/2, T]. The derivative of q is −t² e^{min w 0} ∈ [−T², 0] for every
state, so q decreases and q ≥ q₀ − T³ > −Q: the clamp of q is inactive. Then w' = q/t² ≤ 0, so
w ≤ w₀ ≤ 0 and min w 0 = w. With φ = q/t² the pair (w, φ) solves w' = φ,
φ' = −(2/t)φ − e^w.
-/

namespace Work.Math.GExistsRight
open Set

/-- Clamp of `y` to [−c, c]. -/
noncomputable def cl (c y : ℝ) : ℝ := max (-c) (min c y)

theorem cl_of_abs_le {c y : ℝ} (h : |y| ≤ c) : cl c y = y := by
  unfold cl; rw [abs_le] at h; rw [min_eq_right h.2, max_eq_right h.1]

theorem abs_cl_le {c : ℝ} (hc : 0 ≤ c) (y : ℝ) : |cl c y| ≤ c := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem continuous_cl (c : ℝ) : Continuous (cl c) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem cl_sub (c y z : ℝ) : |cl c y - cl c z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

/-- exp is Lipschitz with constant `exp m` below `m`. -/
theorem exp_sub_le_of_le {a b m : ℝ} (ha : a ≤ m) (hb : b ≤ m) :
    |Real.exp a - Real.exp b| ≤ Real.exp m * |a - b| := by
  have key : ∀ x y : ℝ, y ≤ x → x ≤ m → Real.exp x - Real.exp y ≤ Real.exp m * (x - y) := by
    intro x y hyx hx
    have h1 := Real.add_one_le_exp (y - x)
    have h2 : Real.exp x - Real.exp y = Real.exp x * (1 - Real.exp (y - x)) := by
      rw [Real.exp_sub]; field_simp
    rw [h2]
    have h3 : Real.exp x ≤ Real.exp m := Real.exp_le_exp.2 hx
    have h4 : 1 - Real.exp (y - x) ≤ x - y := by linarith
    have h5 : 0 ≤ 1 - Real.exp (y - x) := by
      have : Real.exp (y - x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith
    calc Real.exp x * (1 - Real.exp (y - x)) ≤ Real.exp m * (1 - Real.exp (y - x)) :=
          mul_le_mul_of_nonneg_right h3 h5
      _ ≤ Real.exp m * (x - y) := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.2 h]), abs_of_nonneg (by linarith)]
    exact key a b h ha
  · rw [abs_of_nonpos (by linarith [Real.exp_le_exp.2 h]), abs_of_nonpos (by linarith)]
    have := key b a h hb
    linarith

/-- The clamped field in (w, q). -/
noncomputable def F (Q : ℝ) (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (cl Q p.2 / t ^ 2, -(t ^ 2 * Real.exp (min p.1 0)))

theorem lipF {Q T t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) T) :
    LipschitzWith (Real.toNNReal (4 + T ^ 2)) (F Q t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hK : (0 : ℝ) ≤ 4 + T ^ 2 := by positivity
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ hK]
  simp only [F, Prod.dist_eq, Real.dist_eq]
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
    have b : 0 ≤ T ^ 2 * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg T) hm0) (sq_nonneg t)
    have h4 : |p.2 - q.2| ≤ (4 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by
      have e : (4 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 =
          4 * (t ^ 2 * max |p.1 - q.1| |p.2 - q.2|) + T ^ 2 * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by
        ring
      rw [e]; linarith
    linarith
  · have e : -(t ^ 2 * Real.exp (min p.1 0)) - -(t ^ 2 * Real.exp (min q.1 0)) =
        -(t ^ 2 * (Real.exp (min p.1 0) - Real.exp (min q.1 0))) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have h1 := exp_sub_le_of_le (min_le_right p.1 0) (min_le_right q.1 0)
    rw [Real.exp_zero, one_mul] at h1
    have h2 : |min p.1 0 - min q.1 0| ≤ |p.1 - q.1| := abs_min_sub_min_le_max _ _ _ _ |>.trans
      (max_le le_rfl (by simp))
    have h3 : |Real.exp (min p.1 0) - Real.exp (min q.1 0)| ≤ max |p.1 - q.1| |p.2 - q.2| :=
      (h1.trans h2).trans hd1
    calc t ^ 2 * |Real.exp (min p.1 0) - Real.exp (min q.1 0)|
        ≤ T ^ 2 * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul htT h3 (abs_nonneg _) (sq_nonneg _)
      _ ≤ (4 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| := by nlinarith

theorem normF {Q T t : ℝ} (hQ : 0 ≤ Q) (ht : t ∈ Icc (1 / 2 : ℝ) T) (p : ℝ × ℝ) :
    ‖F Q t p‖ ≤ 4 * Q + T ^ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht2 : 1 / 4 ≤ t ^ 2 := by nlinarith [ht.1]
  have htT : t ^ 2 ≤ T ^ 2 := by
    have := ht.2; nlinarith [ht.1]
  simp only [F, Prod.norm_def, Real.norm_eq_abs]
  have hc := abs_cl_le hQ p.2
  refine max_le ?_ ?_
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg T, abs_nonneg (cl Q p.2)]
  · rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_pos (Real.exp_pos _)]
    have : Real.exp (min p.1 0) ≤ 1 := Real.exp_le_one_iff.2 (min_le_right _ _)
    nlinarith [Real.exp_pos (min p.1 0)]

theorem contF {Q T : ℝ} (x : ℝ × ℝ) : ContinuousOn (fun t => F Q t x) (Icc (1 / 2 : ℝ) T) := by
  unfold F
  refine ContinuousOn.prodMk ?_ ?_
  · exact continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity
  · exact ((continuousOn_id.pow 2).mul continuousOn_const).neg

theorem fst_derivW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).1) d.1 s t := by
  have := h.hasFDerivWithinAt.fst.hasDerivWithinAt
  simpa using this

theorem snd_derivW {α : ℝ → ℝ × ℝ} {d : ℝ × ℝ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt α d s t) : HasDerivWithinAt (fun r => (α r).2) d.2 s t := by
  have := h.hasFDerivWithinAt.snd.hasDerivWithinAt
  simpa using this

theorem exists_right (T w₀ φ₀ : ℝ) (hT : 1 / 2 ≤ T) (hw₀ : w₀ ≤ 0) (hφ₀ : φ₀ ≤ 0)
    (hφ₀' : -1 ≤ φ₀) :
    ∃ w φ : ℝ → ℝ, w (1 / 2) = w₀ ∧ φ (1 / 2) = φ₀ ∧
      ∀ t ∈ Icc (1 / 2 : ℝ) T, HasDerivWithinAt w (φ t) (Icc (1 / 2) T) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) (Icc (1 / 2) T) t := by
  set Q : ℝ := T ^ 3 + 1 with hQ
  have hT0 : 0 < T := by linarith
  have hQ0 : 0 ≤ Q := by positivity
  set L : ℝ := 4 * Q + T ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  set q₀ : ℝ := φ₀ / 4 with hq₀
  have hPL : IsPicardLindelof (F Q) (tmin := 1 / 2) (tmax := T)
      ⟨1 / 2, le_rfl, hT⟩ (w₀, q₀) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (4 + T ^ 2)) :=
    { lipschitzOnWith := fun t ht => (lipF ht).lipschitzOnWith
      continuousOn := fun x _ => contF x
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact normF hQ0 ht p
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
    fun t ht => by have := fst_derivW (hα t ht); simpa [F] using this
  have dq : ∀ t ∈ Icc (1 / 2 : ℝ) T,
      HasDerivWithinAt q (-(t ^ 2 * Real.exp (min (w t) 0))) (Icc (1 / 2) T) t :=
    fun t ht => by have := snd_derivW (hα t ht); simpa [F] using this
  have cq : ContinuousOn q (Icc (1 / 2) T) := fun t ht => (dq t ht).continuousWithinAt
  have cw : ContinuousOn w (Icc (1 / 2) T) := fun t ht => (dw t ht).continuousWithinAt
  -- q decreases
  have qanti : AntitoneOn q (Icc (1 / 2) T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) cq
      (fun t ht => ((dq t (interior_subset ht)).mono interior_subset))
    intro t _
    have := Real.exp_pos (min (w t) 0)
    nlinarith [sq_nonneg t]
  -- q + T² t increases
  have qmono : MonotoneOn (fun t => q t + T ^ 2 * t) (Icc (1 / 2) T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (cq.add (continuousOn_const.mul continuousOn_id))
      (fun t ht => (((dq t (interior_subset ht)).add
        ((hasDerivAt_id t).const_mul (T ^ 2)).hasDerivWithinAt).mono interior_subset))
    intro t ht
    rw [interior_Icc] at ht
    have h1 : Real.exp (min (w t) 0) ≤ 1 := Real.exp_le_one_iff.2 (min_le_right _ _)
    have h2 : t ^ 2 ≤ T ^ 2 := by nlinarith [ht.1, ht.2]
    have h3 := Real.exp_pos (min (w t) 0)
    simp only [mul_one]
    nlinarith [sq_nonneg t]
  have hm : (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) T := ⟨le_rfl, hT⟩
  have qle : ∀ t ∈ Icc (1 / 2 : ℝ) T, q t ≤ q₀ := fun t ht => by
    rw [← hq0]; exact qanti hm ht ht.1
  have qge : ∀ t ∈ Icc (1 / 2 : ℝ) T, q₀ - T ^ 3 ≤ q t := fun t ht => by
    have h := qmono hm ht ht.1
    simp only [hq0] at h
    have : T ^ 2 * t ≤ T ^ 3 := by
      have := ht.2; nlinarith [sq_nonneg T]
    nlinarith [sq_nonneg T]
  have qin : ∀ t ∈ Icc (1 / 2 : ℝ) T, |q t| ≤ Q := fun t ht => by
    have h1 := qle t ht
    have h2 := qge t ht
    rw [abs_le]; constructor <;> [skip; skip] <;> nlinarith
  have hqcl : ∀ t ∈ Icc (1 / 2 : ℝ) T, cl Q (q t) = q t := fun t ht => cl_of_abs_le (qin t ht)
  -- w decreases
  have wanti : AntitoneOn w (Icc (1 / 2) T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) cw
      (fun t ht => ((dw t (interior_subset ht)).mono interior_subset))
    intro t ht
    have ht' := interior_subset ht
    rw [hqcl t ht']
    have : q t ≤ 0 := (qle t ht').trans (by rw [hq₀]; linarith)
    exact div_nonpos_of_nonpos_of_nonneg this (sq_nonneg t)
  have wle : ∀ t ∈ Icc (1 / 2 : ℝ) T, w t ≤ 0 := fun t ht => by
    have := wanti hm ht ht.1
    rw [hw0] at this; linarith
  refine ⟨w, fun t => q t / t ^ 2, hw0, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [hq0, hq₀]; norm_num; ring
  · have := dw t ht
    rwa [hqcl t ht] at this
  · have ht0 : t ≠ 0 := by have := ht.1; positivity
    have h := (dq t ht).div ((hasDerivAt_pow 2 t).hasDerivWithinAt) (pow_ne_zero 2 ht0)
    rw [min_eq_left (wle t ht)] at h
    convert h using 1
    field_simp
    ring

end Work.Math.GExistsRight

#print axioms Work.Math.GExistsRight.exists_right
