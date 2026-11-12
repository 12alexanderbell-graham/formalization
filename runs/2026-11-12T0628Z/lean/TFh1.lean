import Checked.Trust.NonVacuity
import Checked.Math.ThomasFermi
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Filter Topology

theorem tf_initial_slope_h1 : necessity% Checked.Math.ThomasFermi.tf_initial_slope 1 := by
  refine ⟨fun x => 1 / (1 + Real.sqrt x) ^ 2, fun x => 1 - 1 / (1 + Real.sqrt x) ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := by
      simpa using Real.hasDerivAt_sqrt hx.ne'
    have hb : 0 < 1 + Real.sqrt x := by positivity
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h1 := ((hs.const_add 1).pow 2).inv (by simp only [Pi.pow_apply]; positivity)
    have h2 := (h1.const_mul (-1 : ℝ)).const_add 1
    have key : (1 / (1 + Real.sqrt x) ^ 2) ^ ((3 : ℝ) / 2) = 1 / (1 + Real.sqrt x) ^ 3 := by
      rw [show (1 : ℝ) / (1 + Real.sqrt x) ^ 2 = (1 / (1 + Real.sqrt x)) ^ (2 : ℝ) by
        rw [Real.rpow_two]; field_simp, ← Real.rpow_mul (by positivity)]
      rw [show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [key]
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [Pi.pow_apply]
      field_simp
      ring
    · exact Filter.Eventually.of_forall fun z => by simp [one_div, neg_mul, sub_eq_add_neg]
  · have hc : Continuous fun x : ℝ => 1 - 1 / (1 + Real.sqrt x) ^ 2 := by
      refine continuous_const.sub (continuous_const.div (by fun_prop) fun x => by positivity)
    exact hc.continuousWithinAt
  · simp
  · intro x _; positivity
  · have h1 : Tendsto (fun x : ℝ => 1 + Real.sqrt x) atTop atTop :=
      tendsto_atTop_add_const_left _ _ Real.tendsto_sqrt_atTop
    have h2 := (tendsto_pow_atTop (two_ne_zero)).comp h1
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h2
  · simp only [sub_self, Real.sqrt_zero, add_zero, one_pow, div_one]
    norm_num
