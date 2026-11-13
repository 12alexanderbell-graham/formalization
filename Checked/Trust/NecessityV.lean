import Checked.Trust.NonVacuity
import Checked.Fidelity.FRSpecs
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Hypothesis necessity for the pinning theorem of the flat Ricci scalar: the specification constrains its function only where the scale factor is positive with a derivative near the time and a second derivative at it, and its rescaling and time-translation fields assume that domain, so the program's Ricci scalar shifted by one off the domain still meets it; each domain condition is needed (a negative constant scale factor, a scale factor with a corner, a scale factor whose derivative has a corner). Module `NecessityV`. -/

namespace Checked.Trust.NCW

open Set Filter Topology Checked.Cosmography Checked.Cosmography.FRCosmo Checked.Fidelity

/-- The domain of the Ricci specification. -/
def RD (a : ℝ → ℝ) (t : ℝ) : Prop :=
  0 < a t ∧ ∃ a' a'' : ℝ → ℝ, (∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) ∧ HasDerivAt a' (a'' t) t

theorem rd_exp (c h t : ℝ) (hc : 0 < c) : RD (fun s => c * Real.exp (h * s)) t := by
  have d1 : ∀ s, HasDerivAt (fun s => c * Real.exp (h * s)) (c * h * Real.exp (h * s)) s := fun s => by
    have := (((hasDerivAt_id s).const_mul h).exp).const_mul c
    simp only [id] at this
    convert this using 1; ring
  have d2 : HasDerivAt (fun s => c * h * Real.exp (h * s)) (c * h * h * Real.exp (h * t)) t := by
    have := (((hasDerivAt_id t).const_mul h).exp).const_mul (c * h)
    simp only [id] at this
    convert this using 1; ring
  exact ⟨mul_pos hc (Real.exp_pos _), fun s => c * h * Real.exp (h * s),
    fun s => c * h * h * Real.exp (h * s), Eventually.of_forall d1, d2⟩

theorem rd_pow (p t : ℝ) (ht : 0 < t) : RD (fun s => s ^ p) t := by
  refine ⟨Real.rpow_pos_of_pos ht p, fun s => p * s ^ (p - 1), fun s => p * ((p - 1) * s ^ (p - 1 - 1)), ?_, ?_⟩
  · filter_upwards [lt_mem_nhds ht] with s hs
    exact Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  · exact (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul p

theorem rd_scale {a a' a'' : ℝ → ℝ} {c t : ℝ} (hc : 0 < c) (ha : 0 < a t)
    (h1 : ∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) (h2 : HasDerivAt a' (a'' t) t) :
    RD (fun s => c * a s) t :=
  ⟨mul_pos hc ha, fun s => c * a' s, fun s => c * a'' s, h1.mono fun _ h => h.const_mul c, h2.const_mul c⟩

theorem rd_translate {a a' a'' : ℝ → ℝ} {τ t : ℝ} (ha : 0 < a (t + τ))
    (h1 : ∀ᶠ s in 𝓝 (t + τ), HasDerivAt a (a' s) s) (h2 : HasDerivAt a' (a'' (t + τ)) (t + τ)) :
    RD (fun s => a (s + τ)) t := by
  refine ⟨ha, fun s => a' (s + τ), fun s => a'' (s + τ), ?_, h2.comp_add_const t τ⟩
  have ht : Tendsto (fun s : ℝ => s + τ) (𝓝 t) (𝓝 (t + τ)) :=
    (continuous_id.add continuous_const).tendsto t
  have h1' := ht.eventually h1
  exact h1'.mono fun s h => h.comp_add_const s τ

open Classical in
/-- The program's Ricci scalar, shifted by one off the domain of the specification. -/
noncomputable def ricciOff (a : ℝ → ℝ) (t : ℝ) : ℝ := if RD a t then curv a t else curv a t + 1

theorem ricciOff_spec : RicciFlatFLRWSpec ricciOff where
  law a a' a'' t ha h1 h2 := by
    rw [ricciOff, ite_eq_left ⟨ha, a', a'', h1, h2⟩]; exact curv_meets_spec.law a a' a'' t ha h1 h2
  deSitter c h t hc := by
    rw [ricciOff, ite_eq_left (rd_exp c h t hc)]; exact curv_meets_spec.deSitter c h t hc
  radiation t ht := by
    rw [ricciOff, ite_eq_left (rd_pow _ t ht)]; exact curv_meets_spec.radiation t ht
  matter t ht := by
    rw [ricciOff, ite_eq_left (rd_pow _ t ht)]; exact curv_meets_spec.matter t ht
  scale_invariant a a' a'' c t hc ha h1 h2 := by
    rw [ricciOff, ricciOff, ite_eq_left (rd_scale hc ha h1 h2), ite_eq_left ⟨ha, a', a'', h1, h2⟩]
    exact curv_meets_spec.scale_invariant a a' a'' c t hc ha h1 h2
  time_translation a a' a'' τ t ha h1 h2 := by
    rw [ricciOff, ricciOff, ite_eq_left (rd_translate ha h1 h2), ite_eq_left ⟨ha, a', a'', h1, h2⟩]
    exact curv_meets_spec.time_translation a a' a'' τ t ha h1 h2

theorem ricciOff_off {a : ℝ → ℝ} {t : ℝ} (h : ¬ RD a t) : ¬ ricciOff a t = curv a t := by
  rw [ricciOff, ite_eq_right h]; simp

theorem abs_not_diff : ¬ DifferentiableAt ℝ (fun s : ℝ => |s|) 0 := not_differentiableAt_abs_zero

/-- Positivity of the scale factor is needed in `ricciSpec_pins`. -/
theorem ricciSpec_pins_h2 : necessity% Checked.Fidelity.ricciSpec_pins 2 := by
  refine ⟨ricciOff, ricciOff_spec, fun _ => -1, fun _ => 0, fun _ => 0, 0,
    Eventually.of_forall fun s => hasDerivAt_const s (-1 : ℝ), hasDerivAt_const 0 (0 : ℝ), ricciOff_off ?_⟩
  intro h; have := h.1; norm_num at this

/-- A derivative of the scale factor near the time is needed in `ricciSpec_pins` (a corner at the time). -/
theorem ricciSpec_pins_h3 : necessity% Checked.Fidelity.ricciSpec_pins 3 := by
  refine ⟨ricciOff, ricciOff_spec, fun s => 1 + |s|, fun _ => 0, fun _ => 0, 0, by norm_num,
    hasDerivAt_const 0 (0 : ℝ), ricciOff_off ?_⟩
  rintro ⟨-, a', -, h1, -⟩
  have hd := (h1.self_of_nhds).differentiableAt
  apply abs_not_diff
  have := (hd.const_add (-1))
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp

/-- The scale factor 1 + ∫₀^s |x| dx: derivative |s| everywhere, no second derivative at 0. -/
noncomputable def cornerD (s : ℝ) : ℝ := 1 + ∫ x in (0 : ℝ)..s, abs x

theorem cornerD_deriv (s : ℝ) : HasDerivAt cornerD |s| s :=
  ((continuous_abs.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add 1

/-- A second derivative at the time is needed in `ricciSpec_pins` (a derivative with a corner). -/
theorem ricciSpec_pins_h4 : necessity% Checked.Fidelity.ricciSpec_pins 4 := by
  refine ⟨ricciOff, ricciOff_spec, cornerD, fun s => |s|, fun _ => 0, 0, by simp [cornerD],
    Eventually.of_forall cornerD_deriv, ricciOff_off ?_⟩
  rintro ⟨-, a', a'', h1, h2⟩
  have heq : a' =ᶠ[𝓝 0] fun s => |s| :=
    h1.mono fun s h => h.unique (cornerD_deriv s)
  exact abs_not_diff (h2.congr_of_eventuallyEq heq.symm).differentiableAt

end Checked.Trust.NCW
