import Checked.Trust.NecessityL
import Checked.Trust.NecessityD

namespace Checked.Trust.NecessityAD3
open Filter Topology
open Checked.Cosmography

theorem dmul_iff (c : ℝ) (hc : c ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun s => c * f s) t ↔ DifferentiableAt ℝ f t := by
  refine ⟨fun h => ?_, fun h => h.const_mul c⟩
  have := h.const_mul c⁻¹
  convert this using 1; funext s; field_simp

theorem dadd_iff (τ : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun s => f (s + τ)) t ↔ DifferentiableAt ℝ f (t + τ) := by
  refine ⟨fun h => ?_, fun h => h.comp t ((differentiableAt_id).add_const τ)⟩
  have h2 : DifferentiableAt ℝ (fun s => s - τ) (t + τ) := differentiableAt_id.sub_const τ
  have := (show DifferentiableAt ℝ (fun s => f (s + τ)) ((t + τ) - τ) by simpa using h).comp (t + τ) h2
  convert this using 1; funext s; simp

theorem dneg_iff (f : ℝ → ℝ) (t : ℝ) :
    DifferentiableAt ℝ (fun s => -f (-s)) t ↔ DifferentiableAt ℝ f (-t) := by
  refine ⟨fun h => ?_, fun h => (h.comp t differentiableAt_id.neg).neg⟩
  have := ((show DifferentiableAt ℝ (fun s => -f (-s)) (-(-t)) by simpa using h).comp (-t)
    differentiableAt_id.neg).neg
  convert this using 1; funext s; simp

open Classical in
/-- `decel` where `ȧ` is differentiable at `t`, `decel + 1` elsewhere. -/
noncomputable def decelDiff2 (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  if DifferentiableAt ℝ (deriv a) t then decel a t else decel a t + 1

theorem rpow_d2 (n t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ (deriv fun s : ℝ => s ^ n) t := by
  have e : (fun s => n * s ^ (n - 1)) =ᶠ[𝓝 t] deriv fun s : ℝ => s ^ n := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact (Real.hasDerivAt_rpow_const (Or.inl hs.ne')).deriv.symm
  exact ((Real.hasDerivAt_rpow_const (p := n - 1) (Or.inl ht.ne')).differentiableAt.const_mul n).congr_of_eventuallyEq e.symm

theorem decelDiff2_spec : Checked.Fidelity.DecelSpec decelDiff2 := by
  have M := Checked.Fidelity.decel_meets_spec
  have D : ∀ (a : ℝ → ℝ) (t : ℝ), DifferentiableAt ℝ (deriv a) t → decelDiff2 a t = decel a t :=
    fun a t h => by rw [decelDiff2, ite_eq_left h]
  refine ⟨fun a a' a'' t h1 h2 ha hd => ?_, fun h t hh => ?_, fun n t hn ht => ?_, fun t ht => ?_,
    fun n t hn ht => ?_, fun c hc a t hd => ?_, fun τ a t hd => ?_, fun a t hd => ?_⟩
  · have e : deriv a =ᶠ[𝓝 t] a' := h1.mono fun s hs => hs.deriv
    rw [D _ _ (h2.differentiableAt.congr_of_eventuallyEq e)]; exact M.formula a a' a'' t h1 h2 ha hd
  · have e : deriv (fun s => Real.exp (h * s)) = fun s => h * Real.exp (h * s) :=
      funext fun s => (Checked.Fidelity.ms_hasDerivAt_expMul h s).deriv
    have hD : DifferentiableAt ℝ (deriv fun s => Real.exp (h * s)) t := by
      rw [e]; fun_prop
    rw [D _ _ hD]; exact M.deSitter h t hh
  · rw [D _ _ (rpow_d2 n t ht)]; exact M.powerLaw n t hn ht
  · rw [D _ _ (rpow_d2 _ t ht)]; exact M.eds t ht
  · have e : deriv (fun s : ℝ => (-s) ^ n) = fun s => -deriv (fun s : ℝ => s ^ n) (-s) :=
      funext fun s => deriv_comp_neg (fun s : ℝ => s ^ n) s
    have hD : DifferentiableAt ℝ (deriv fun s : ℝ => (-s) ^ n) t := by
      rw [e]; exact (dneg_iff _ t).2 (rpow_d2 n (-t) (by linarith))
    rw [D _ _ hD]; exact M.crunch n t hn ht
  · have e : deriv (fun s => c * a s) = fun s => c * deriv a s :=
      funext fun s => by rw [deriv_const_mul_field']
    have hM := M.rescale c hc a t hd
    unfold decelDiff2
    rw [e]
    by_cases h : DifferentiableAt ℝ (deriv a) t
    · rw [ite_eq_left h, ite_eq_left ((dmul_iff c hc.ne' _ t).2 h), hM]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((dmul_iff c hc.ne' _ t).1 h')), hM]
  · have e : deriv (fun s => a (s + τ)) = fun s => deriv a (s + τ) :=
      funext fun s => deriv_comp_add_const a τ s
    have hM := M.translate τ a t hd
    unfold decelDiff2
    rw [e]
    by_cases h : DifferentiableAt ℝ (deriv a) (t + τ)
    · rw [ite_eq_left h, ite_eq_left ((dadd_iff τ _ t).2 h), hM]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((dadd_iff τ _ t).1 h')), hM]
  · have e : deriv (fun s => a (-s)) = fun s => -deriv a (-s) :=
      funext fun s => deriv_comp_neg a s
    have hM := M.timeReverse a t hd
    unfold decelDiff2
    rw [e]
    by_cases h : DifferentiableAt ℝ (deriv a) (-t)
    · rw [ite_eq_left h, ite_eq_left ((dneg_iff _ t).2 h), hM]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ((dneg_iff _ t).1 h')), hM]

theorem decelSpec_pins_h3 : necessity% Checked.Fidelity.decelSpec_pins 3 := by
  have hnd : ¬ DifferentiableAt ℝ (deriv (Checked.Trust.NCD.kink 0)) 0 := fun h => by
    rw [Checked.Trust.NCD.kink_deriv] at h
    apply not_differentiableAt_abs_zero
    have := (h.const_add (-1)).const_mul (1 / 2 : ℝ)
    convert this using 1; funext s; push_cast; ring
  refine ⟨decelDiff2, decelDiff2_spec, Checked.Trust.NCD.kink 0, fun s => 1 + 2 * |s|, 0, 0,
    Eventually.of_forall fun s => ?_, by simp [Checked.Trust.NCD.kink], by norm_num, ?_⟩
  · convert Checked.Trust.NCD.kink_hasDerivAt 0 s using 1; push_cast; ring
  · rw [decelDiff2, ite_eq_right hnd]; norm_num

end Checked.Trust.NecessityAD3
