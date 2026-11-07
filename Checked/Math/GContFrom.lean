import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.PicardLindelof
import Checked.Math.GExistsRight

/-! Gelfand PDE, `GContFrom`: continuation of solutions of the radial Gelfand equation from any positive start with non-positive value and slope. Promoted from `Work/Math/GContFrom.lean`. -/

namespace Checked.Math.GContFrom
open Set Checked.Math.GExistsRight

theorem lipF' {Q T a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a T) :
    LipschitzWith (Real.toNNReal (1 / a ^ 2 + T ^ 2)) (F Q t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hK : (0 : ℝ) ≤ 1 / a ^ 2 + T ^ 2 := by positivity
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ hK]
  simp only [F, Prod.dist_eq, Real.dist_eq]
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hm0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := (abs_nonneg _).trans hd1
  have ht2 : a ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
  have htT : t ^ 2 ≤ T ^ 2 := by
    have := ht.2; nlinarith [ht.1]
  have ha2 : 0 < a ^ 2 := by positivity
  refine max_le ?_ ?_
  · rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    have := cl_sub Q p.2 q.2
    have h1 : 1 ≤ 1 / a ^ 2 * t ^ 2 := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha2]; linarith
    have b : 0 ≤ T ^ 2 * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg T) hm0) (sq_nonneg t)
    have h4 : |p.2 - q.2| ≤ (1 / a ^ 2 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by
      have e : (1 / a ^ 2 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 =
          (1 / a ^ 2 * t ^ 2) * max |p.1 - q.1| |p.2 - q.2| +
            T ^ 2 * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by ring
      rw [e]; nlinarith
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
    have h5 : 0 ≤ 1 / a ^ 2 * max |p.1 - q.1| |p.2 - q.2| := by positivity
    calc t ^ 2 * |Real.exp (min p.1 0) - Real.exp (min q.1 0)|
        ≤ T ^ 2 * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul htT h3 (abs_nonneg _) (sq_nonneg _)
      _ ≤ (1 / a ^ 2 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| := by nlinarith

theorem normF' {Q T a t : ℝ} (ha : 0 < a) (hQ : 0 ≤ Q) (ht : t ∈ Icc a T) (p : ℝ × ℝ) :
    ‖F Q t p‖ ≤ Q / a ^ 2 + T ^ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht2 : a ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
  have htT : t ^ 2 ≤ T ^ 2 := by
    have := ht.2; nlinarith [ht.1]
  have ha2 : 0 < a ^ 2 := by positivity
  simp only [F, Prod.norm_def, Real.norm_eq_abs]
  have hc := abs_cl_le hQ p.2
  refine max_le ?_ ?_
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    have h1 : |cl Q p.2| / t ^ 2 ≤ Q / a ^ 2 :=
      div_le_div₀ hQ hc ha2 ht2
    have : 0 ≤ T ^ 2 := sq_nonneg T
    linarith
  · rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_pos (Real.exp_pos _)]
    have : Real.exp (min p.1 0) ≤ 1 := Real.exp_le_one_iff.2 (min_le_right _ _)
    have : 0 ≤ Q / a ^ 2 := by positivity
    nlinarith [Real.exp_pos (min p.1 0)]

theorem contF' {Q T a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    ContinuousOn (fun t => F Q t x) (Icc a T) := by
  unfold F
  refine ContinuousOn.prodMk ?_ ?_
  · exact continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity
  · exact ((continuousOn_id.pow 2).mul continuousOn_const).neg

theorem exists_from (a T w₀ φ₀ : ℝ) (ha : 0 < a) (hT : a ≤ T) (hw₀ : w₀ ≤ 0) (hφ₀ : φ₀ ≤ 0) :
    ∃ w φ : ℝ → ℝ, w a = w₀ ∧ φ a = φ₀ ∧
      ∀ t ∈ Icc a T, HasDerivWithinAt w (φ t) (Icc a T) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) (Icc a T) t := by
  set q₀ : ℝ := a ^ 2 * φ₀ with hq₀
  have hq₀n : q₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hφ₀
  set Q : ℝ := T ^ 3 - q₀ with hQ
  have hT0 : 0 < T := by linarith
  have hQ0 : 0 ≤ Q := by have := pow_pos hT0 3; linarith
  set L : ℝ := Q / a ^ 2 + T ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (F Q) (tmin := a) (tmax := T)
      ⟨a, le_rfl, hT⟩ (w₀, q₀) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (1 / a ^ 2 + T ^ 2)) :=
    { lipschitzOnWith := fun t ht => (lipF' ha ht).lipschitzOnWith
      continuousOn := fun x _ => contF' ha x
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact normF' ha hQ0 ht p
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
  have hw0 : w a = w₀ := by simp only [hw, h0]
  have hq0 : q a = q₀ := by simp only [hq, h0]
  have dw : ∀ t ∈ Icc a T, HasDerivWithinAt w (cl Q (q t) / t ^ 2) (Icc a T) t :=
    fun t ht => by have := fst_derivW (hα t ht); simpa [F] using this
  have dq : ∀ t ∈ Icc a T,
      HasDerivWithinAt q (-(t ^ 2 * Real.exp (min (w t) 0))) (Icc a T) t :=
    fun t ht => by have := snd_derivW (hα t ht); simpa [F] using this
  have cq : ContinuousOn q (Icc a T) := fun t ht => (dq t ht).continuousWithinAt
  have cw : ContinuousOn w (Icc a T) := fun t ht => (dw t ht).continuousWithinAt
  have qanti : AntitoneOn q (Icc a T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) cq
      (fun t ht => ((dq t (interior_subset ht)).mono interior_subset))
    intro t _
    have := Real.exp_pos (min (w t) 0)
    nlinarith [sq_nonneg t]
  have qmono : MonotoneOn (fun t => q t + T ^ 2 * t) (Icc a T) := by
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
  have hm : a ∈ Icc a T := ⟨le_rfl, hT⟩
  have qle : ∀ t ∈ Icc a T, q t ≤ q₀ := fun t ht => by
    rw [← hq0]; exact qanti hm ht ht.1
  have qge : ∀ t ∈ Icc a T, q₀ - T ^ 3 ≤ q t := fun t ht => by
    have h := qmono hm ht ht.1
    simp only [hq0] at h
    have h1 : T ^ 2 * t ≤ T ^ 3 := by
      have := ht.2; nlinarith [sq_nonneg T]
    have h2 : 0 ≤ T ^ 2 * a := by positivity
    nlinarith [sq_nonneg T]
  have qin : ∀ t ∈ Icc a T, |q t| ≤ Q := fun t ht => by
    have h1 := qle t ht
    have h2 := qge t ht
    have h3 := pow_pos hT0 3
    rw [abs_le]; constructor <;> linarith
  have hqcl : ∀ t ∈ Icc a T, cl Q (q t) = q t := fun t ht => cl_of_abs_le (qin t ht)
  have wanti : AntitoneOn w (Icc a T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) cw
      (fun t ht => ((dw t (interior_subset ht)).mono interior_subset))
    intro t ht
    have ht' := interior_subset ht
    rw [hqcl t ht']
    have : q t ≤ 0 := (qle t ht').trans hq₀n
    exact div_nonpos_of_nonpos_of_nonneg this (sq_nonneg t)
  have wle : ∀ t ∈ Icc a T, w t ≤ 0 := fun t ht => by
    have := wanti hm ht ht.1
    rw [hw0] at this; linarith
  refine ⟨w, fun t => q t / t ^ 2, hw0, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [hq0, hq₀]; field_simp
  · have := dw t ht
    rwa [hqcl t ht] at this
  · have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
    have h := (dq t ht).div ((hasDerivAt_pow 2 t).hasDerivWithinAt) (pow_ne_zero 2 ht0)
    rw [min_eq_left (wle t ht)] at h
    convert h using 1
    field_simp
    ring

end Checked.Math.GContFrom
