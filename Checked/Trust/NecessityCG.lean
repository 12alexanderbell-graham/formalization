import Checked.Cosmography.FREta
import Checked.Trust.NonVacuity

/-! Hypothesis necessity for `Checked.Cosmography.FREta.eta_ratios` (run 2026-11-27T1228Z): the condition that the
corrected curvature quantity is not zero is NEEDED (hypothesis 3). The witness is a vacuum model (density parameter
zero) of the metric F(R) setting whose expansion rate grows linearly in time: the scale factor is the exponential of
three halves of the squared time, observed at time one, and F is a quadratic polynomial in the curvature. Along this
scale factor the curvature and the derivative of F are both affine in the squared expansion rate, so the master
equation holds at every time, and the derivatives of F of order three and four vanish everywhere. At the observation
time the deceleration is minus four thirds, the jerk two, the snap ten thirds and the lerk six: the corrected
curvature quantity is zero, the jerk combination is four thirds, F at today's curvature is minus eighteen, and the
second derivative of F is minus one seventy second. The first ratio of the review is then a division by zero (the
combination of the snap-free polynomials at density zero vanishes too, as the first relation of `fR_values` forces),
so Lean's value of the right side is zero while the left side is one sixteenth. Found as the member of the
linear-expansion-rate vacuum family where the corrected quantity vanishes alone
(`runs/2026-11-27T1228Z/scripts/linH.py`). -/

namespace Checked.Trust.NecessityCG
open Real Filter Topology Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.FRCosmo
  Checked.Cosmography.FREta

/-! ## The scale factor -/

/-- Scale factor of the model: the exponential of three halves of the squared time. -/
noncomputable def gA : ℝ → ℝ := fun t => Real.exp (3 * t ^ 2 / 2)

lemma gA_pos (t : ℝ) : 0 < gA t := Real.exp_pos _

lemma gA_hd (t : ℝ) : HasDerivAt gA (3 * t * gA t) t := by
  have h : HasDerivAt (fun t : ℝ => 3 * t ^ 2 / 2) (3 * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (3 : ℝ)).div_const 2
    convert this using 1; push_cast; ring
  have h2 : HasDerivAt (fun x => Real.exp (3 * x ^ 2 / 2)) (Real.exp (3 * t ^ 2 / 2) * (3 * t)) t := h.exp
  exact h2.congr_deriv (by show _ = 3 * t * Real.exp (3 * t ^ 2 / 2); ring)

/-- A polynomial factor times the scale factor: the product rule. -/
lemma prod_hd {P : ℝ → ℝ} {P' : ℝ} {t : ℝ} (hP : HasDerivAt P P' t) :
    HasDerivAt (fun t => P t * gA t) ((P' + 3 * t * P t) * gA t) t := by
  convert hP.mul (gA_hd t) using 1; ring

lemma gA_d1 : deriv gA = fun t => 3 * t * gA t := by
  funext t; exact (gA_hd t).deriv

lemma gA_d2 : deriv^[2] gA = fun t => (3 + 9 * t ^ 2) * gA t := by
  rw [Function.iterate_succ_apply', Function.iterate_one, gA_d1]
  funext t
  have hP : HasDerivAt (fun t : ℝ => 3 * t) 3 t := by simpa using (hasDerivAt_id t).const_mul (3 : ℝ)
  rw [(prod_hd hP).deriv]; ring

lemma gA_d3 : deriv^[3] gA = fun t => (27 * t + 27 * t ^ 3) * gA t := by
  rw [Function.iterate_succ_apply', gA_d2]
  funext t
  have hP : HasDerivAt (fun t : ℝ => 3 + 9 * t ^ 2) (18 * t) t :=
    (((hasDerivAt_pow 2 t).const_mul (9 : ℝ)).const_add 3).congr_deriv (by push_cast; ring)
  rw [(prod_hd hP).deriv]; ring

lemma gA_d4 : deriv^[4] gA = fun t => (27 + 162 * t ^ 2 + 81 * t ^ 4) * gA t := by
  rw [Function.iterate_succ_apply', gA_d3]
  funext t
  have hP : HasDerivAt (fun t : ℝ => 27 * t + 27 * t ^ 3) (27 + 81 * t ^ 2) t :=
    (((hasDerivAt_id' t).const_mul (27 : ℝ)).add ((hasDerivAt_pow 3 t).const_mul (27 : ℝ))).congr_deriv
      (by push_cast; ring)
  rw [(prod_hd hP).deriv]; ring

lemma gA_d5 : deriv^[5] gA = fun t => (405 * t + 810 * t ^ 3 + 243 * t ^ 5) * gA t := by
  rw [Function.iterate_succ_apply', gA_d4]
  funext t
  have hP : HasDerivAt (fun t : ℝ => 27 + 162 * t ^ 2 + 81 * t ^ 4) (324 * t + 324 * t ^ 3) t :=
    ((((hasDerivAt_pow 2 t).const_mul (162 : ℝ)).const_add 27).add
      ((hasDerivAt_pow 4 t).const_mul (81 : ℝ))).congr_deriv (by push_cast; ring)
  rw [(prod_hd hP).deriv]; ring

lemma gA_hubble : hubble gA = fun t => 3 * t := by
  funext t
  unfold hubble
  rw [gA_d1]
  field_simp [(gA_pos t).ne']

lemma gA_dhubble : deriv (hubble gA) = fun _ => 3 := by
  rw [gA_hubble]
  funext t
  simp

lemma gA_curv : curv gA = fun t => -18 - 108 * t ^ 2 := by
  funext t
  unfold curv
  rw [gA_dhubble, gA_hubble]
  ring

lemma gA_dcurv : deriv (curv gA) = fun t => -216 * t := by
  rw [gA_curv]
  funext t
  have := ((hasDerivAt_pow 2 t).const_mul (108 : ℝ)).const_sub (-18)
  rw [show (fun t : ℝ => -18 - 108 * t ^ 2) = fun t => -18 - 108 * t ^ 2 from rfl, this.deriv]
  push_cast; ring

lemma gA_d2curv : deriv^[2] (curv gA) = fun _ => -216 := by
  rw [Function.iterate_succ_apply', Function.iterate_one, gA_dcurv]
  funext t
  simp

/-! ## The function F -/

/-- F of the model: a quadratic polynomial in the curvature. -/
noncomputable def gF : ℝ → ℝ := fun R => -(R ^ 2 / 144) - 3 * R / 4 - 9 / 4

lemma gF_d1 : deriv gF = fun R => -(R / 72) - 3 / 4 := by
  funext R
  have h := (((hasDerivAt_pow 2 R).div_const 144).neg.sub ((hasDerivAt_id R).const_mul (3 : ℝ) |>.div_const 4)).sub_const
    (9 / 4 : ℝ)
  have h' : HasDerivAt gF _ R := h
  rw [h'.deriv]; push_cast; ring

lemma gF_d2 : deriv^[2] gF = fun _ => -(1 / 72) := by
  rw [Function.iterate_succ_apply', Function.iterate_one, gF_d1]
  funext R
  have h := ((hasDerivAt_id R).div_const 72).neg.sub_const (3 / 4 : ℝ)
  have h' : HasDerivAt (fun R : ℝ => -(R / 72) - 3 / 4) _ R := h
  rw [h'.deriv]

lemma gF_d3 : deriv^[3] gF = fun _ => 0 := by
  rw [Function.iterate_succ_apply', gF_d2]
  funext R; simp

lemma gF_d4 : deriv^[4] gF = fun _ => 0 := by
  rw [Function.iterate_succ_apply', gF_d3]
  funext R; simp

/-! ## The model -/

theorem lin_model : IsFRCosmo 0 gA gF 1 := by
  have hc : curv gA 1 = -126 := by rw [gA_curv]; norm_num
  refine ⟨gA_pos 1, by rw [gA_hubble]; norm_num,
    (by unfold gA; fun_prop : ContDiff ℝ 5 gA).contDiffAt,
    (by unfold gF; fun_prop : ContDiff ℝ 4 gF), ?_, ?_, ?_, ?_⟩
  · unfold FriedmannEq rhoM
    rw [gF_d1, gF_d2, gA_hubble, gA_dcurv, hc]
    unfold gF
    norm_num
  · refine Filter.Eventually.of_forall fun t => ?_
    unfold MasterEq rhoM
    rw [gF_d1, gF_d2, gF_d3, gA_dhubble, gA_hubble, gA_dcurv, gA_d2curv, gA_curv]
    ring
  · rw [gF_d1, hc]; norm_num
  · rw [gF_d4]

theorem lin_facts :
    decel gA 1 = -4 / 3 ∧ cosmoCoeff 3 gA 1 = 2 ∧ cosmoCoeff 4 gA 1 = 10 / 3 ∧
      cosmoCoeff 5 gA 1 = 6 ∧ hubble gA 1 = 3 ∧ gF (curv gA 1) = -18 ∧
      deriv^[2] gF (curv gA 1) = -(1 / 72) := by
  have hg := (gA_pos 1).ne'
  have h2 : deriv (deriv gA) 1 = (3 + 9 * 1 ^ 2) * gA 1 := by
    have := congrFun gA_d2 1
    simpa only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] using this
  refine ⟨?_, ?_, ?_, ?_, by rw [gA_hubble]; norm_num, ?_, by rw [gF_d2]⟩
  · unfold decel
    rw [h2, gA_d1]
    field_simp
    norm_num
  · unfold cosmoCoeff
    rw [iteratedDeriv_eq_iterate, gA_d3, gA_hubble]
    field_simp
    norm_num
  · unfold cosmoCoeff
    rw [iteratedDeriv_eq_iterate, gA_d4, gA_hubble]
    field_simp
    norm_num
  · unfold cosmoCoeff
    rw [iteratedDeriv_eq_iterate, gA_d5, gA_hubble]
    field_simp
    norm_num
  · rw [gA_curv]; unfold gF; norm_num

/-- The condition that the corrected curvature quantity is not zero is needed in `eta_ratios`: the vacuum model with
a linearly growing expansion rate, where that quantity vanishes alone. -/
theorem eta_ratios_h3 : necessity% Checked.Cosmography.FREta.eta_ratios 3 := by
  obtain ⟨hq, hj, hs, hl, hH, hF, hF2⟩ := lin_facts
  refine ⟨0, gA, gF, 1, lin_model, ?_, ?_, ?_⟩
  · rw [hF]; norm_num
  · rw [hq, hj]; norm_num
  · intro h
    have h1 := h.1
    rw [hF2, hH, hF, hq, hj, hs, hl] at h1
    unfold eta20Of P2 Q2 P0 Q0 at h1
    norm_num at h1

end Checked.Trust.NecessityCG
