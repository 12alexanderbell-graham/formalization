import Checked.Trust.NecessityL

namespace Checked.Trust.NecessityAD
open Filter Topology
open Checked.Cosmography

open Classical in
/-- `decel` where `a` is differentiable at `t`, `decel + 1` elsewhere. -/
noncomputable def decelDiff (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  if DifferentiableAt ℝ a t then decel a t else decel a t + 1

theorem decelDiff_spec : Checked.Fidelity.DecelSpec decelDiff := by
  have M := Checked.Fidelity.decel_meets_spec
  have D : ∀ (a : ℝ → ℝ) (t : ℝ), deriv a t ≠ 0 → decelDiff a t = decel a t := fun a t h => by
    rw [decelDiff, ite_eq_left (differentiableAt_of_deriv_ne_zero h)]
  refine ⟨fun a a' a'' t h1 h2 ha hd => ?_, fun h t hh => ?_, fun n t hn ht => ?_, fun t ht => ?_,
    fun n t hn ht => ?_, fun c hc a t hd => ?_, fun τ a t hd => ?_, fun a t hd => ?_⟩
  · rw [decelDiff, ite_eq_left (h1.self_of_nhds).differentiableAt]; exact M.formula a a' a'' t h1 h2 ha hd
  · have hD : deriv (fun s => Real.exp (h * s)) t ≠ 0 := by
      rw [(Checked.Fidelity.ms_hasDerivAt_expMul h t).deriv]
      exact mul_ne_zero hh (Real.exp_pos _).ne'
    rw [D _ _ hD]; exact M.deSitter h t hh
  · rw [D _ _ (Checked.Trust.NCL.rpow_deriv_ne n t hn ht)]; exact M.powerLaw n t hn ht
  · rw [D _ _ (Checked.Trust.NCL.rpow_deriv_ne _ t (by norm_num) ht)]; exact M.eds t ht
  · have hD : deriv (fun s : ℝ => (-s) ^ n) t ≠ 0 := by
      rw [deriv_comp_neg (fun s : ℝ => s ^ n) t]
      exact neg_ne_zero.2 (Checked.Trust.NCL.rpow_deriv_ne n (-t) hn (by linarith))
    rw [D _ _ hD]; exact M.crunch n t hn ht
  · have hD : deriv (fun s => c * a s) t ≠ 0 := by
      rw [deriv_const_mul_field']; exact mul_ne_zero hc.ne' hd
    rw [D _ _ hD, D _ _ hd]; exact M.rescale c hc a t hd
  · have hD : deriv (fun s => a (s + τ)) t ≠ 0 := by rw [deriv_comp_add_const]; exact hd
    rw [D _ _ hD, D _ _ hd]; exact M.translate τ a t hd
  · have hD : deriv (fun s => a (-s)) t ≠ 0 := by rw [deriv_comp_neg]; exact neg_ne_zero.2 hd
    rw [D _ _ hD, D _ _ hd]; exact M.timeReverse a t hd

/-- The derivative hypothesis `ȧ = a'` near `t` is needed in `decelSpec_pins`: `decelDiff` meets
`DecelSpec` (every clause of the specification is about a scale factor differentiable at the time
considered), and at `a = 1 + |s|`, `t = 0`, with `a' = 1`, `a'' = 0` (so `a'` has derivative `a''`,
`a(0) > 0`, `a'(0) ≠ 0`), `a` is not differentiable at `0` and `decelDiff a 0 = decel a 0 + 1`. -/
theorem decelSpec_pins_h2 : necessity% Checked.Fidelity.decelSpec_pins 2 := by
  have hnd : ¬ DifferentiableAt ℝ (fun s : ℝ => 1 + |s|) 0 := fun h => by
    apply not_differentiableAt_abs_zero
    have := h.const_add (-1)
    convert this using 1; funext s; ring
  refine ⟨decelDiff, decelDiff_spec, fun s => 1 + |s|, fun _ => 1, 0, 0, hasDerivAt_const _ _,
    by norm_num, one_ne_zero, ?_⟩
  rw [decelDiff, ite_eq_right hnd]; norm_num

end Checked.Trust.NecessityAD
