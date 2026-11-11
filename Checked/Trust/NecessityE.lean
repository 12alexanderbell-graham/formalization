import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationPrinted
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hypothesis necessity witnesses, the printed separation value (trust track T2b, run 2026-11-11T0828Z)

Profile `p = 1 − e^{−k η²}`, `q = p' = 2 k η e^{−k η²}` with `k = 1988376 / 20000000`, so that `q'(0) = 2k`
equals `0.1988376`: it starts at `p = q = 0`, tends to `1`, has `q > 0` beyond the wall and
`q / (1 − p) = 2 k η → ∞`. With `f = ∫ p` it solves no Falkner–Skan equation (the equation hypothesis
is needed); with `f = −(q' + c(1 − p²)) / q` (`c` the printed value, junk value `0` at the wall, where the
equation holds because `q'(0) = −c`) it solves the equation but `f' ≠ p` (the hypothesis `f' = p` is
needed). In both cases β is the printed value, so the conclusion `β ≠ −0.1988376` is false.
-/

open Set Filter Topology

namespace Checked.Trust.NCP

noncomputable def kP : ℝ := 1988376 / 20000000
noncomputable def prP (η : ℝ) : ℝ := 1 - Real.exp (-(kP * η ^ 2))
noncomputable def prQ (η : ℝ) : ℝ := 2 * kP * η * Real.exp (-(kP * η ^ 2))
noncomputable def prQ' (η : ℝ) : ℝ := (2 * kP - 4 * kP ^ 2 * η ^ 2) * Real.exp (-(kP * η ^ 2))

theorem kP_pos : 0 < kP := by unfold kP; norm_num

theorem pr_exp_deriv (η : ℝ) :
    HasDerivAt (fun η : ℝ => Real.exp (-(kP * η ^ 2))) (-(2 * kP * η) * Real.exp (-(kP * η ^ 2))) η := by
  have := (((hasDerivAt_pow 2 η).const_mul kP).neg).exp
  convert this using 1; push_cast; ring

theorem prP_deriv (η : ℝ) : HasDerivAt prP (prQ η) η := by
  have := (pr_exp_deriv η).const_sub 1
  unfold prP prQ; convert this using 1; ring

theorem prQ_deriv (η : ℝ) : HasDerivAt prQ (prQ' η) η := by
  have h := ((hasDerivAt_id η).const_mul (2 * kP)).mul (pr_exp_deriv η)
  unfold prQ prQ'; convert h using 1 <;> simp only [id]; ring

theorem prP_zero : prP 0 = 0 := by simp [prP]
theorem prQ_zero : prQ 0 = 0 := by simp [prQ]

theorem prQ_pos : ∀ η ∈ Ioi (0 : ℝ), 0 < prQ η := by
  intro η hη; have : (0 : ℝ) < η := hη; have := kP_pos; unfold prQ; positivity

theorem prP_lim : Tendsto prP atTop (𝓝 1) := by
  have hu : Tendsto (fun η : ℝ => kP * η ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).const_mul_atTop kP_pos
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hu
  have := h.const_sub 1
  simp only [sub_zero] at this
  exact this.congr fun η => rfl

theorem pr_decay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - prP η) ≤ prQ η := by
  intro M
  filter_upwards [eventually_ge_atTop (|M| / (2 * kP))] with η hη
  have hk := kP_pos
  have he := Real.exp_pos (-(kP * η ^ 2))
  have key : M ≤ 2 * kP * η := by
    have : |M| ≤ 2 * kP * η := by
      rw [div_le_iff₀ (by positivity)] at hη; linarith
    linarith [le_abs_self M]
  have e1 : 1 - prP η = Real.exp (-(kP * η ^ 2)) := by unfold prP; ring
  rw [e1]; unfold prQ
  exact mul_le_mul_of_nonneg_right key he.le

noncomputable def prF (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, prP s

theorem prP_cont : Continuous prP := by unfold prP; fun_prop

theorem prF_deriv (η : ℝ) : HasDerivAt prF (prP η) η :=
  (prP_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

/-- `g = −(q' + c (1 − p²)) / q` beyond the wall, junk `0` at the wall. -/
noncomputable def prG (η : ℝ) : ℝ :=
  if η = 0 then 0 else -((prQ' η + -(1988376 / 10000000) * (1 - prP η ^ 2)) / prQ η)

theorem prG_ode (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) :
    prQ' η = -(prG η * prQ η) - -(1988376 / 10000000 : ℝ) * (1 - prP η ^ 2) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ η from hη) with h | h
  · subst h; simp only [prQ', prG, prQ_zero, prP_zero, ite_true, kP]; norm_num
  · have hq := prQ_pos η h
    simp only [prG, h.ne', ite_false]
    field_simp
    ring

/-- `f' = p` is needed in `fs_separation_not_printed_value`: the profile above with `f = −(q' + c(1 − p²))/q`
solves the equation at the printed `β = c`, meets every boundary and decay condition, and β equals `c`. -/
theorem fs_separation_not_printed_value_h1 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_not_printed_value 1 := by
  refine ⟨-(1988376 / 10000000), prG, prP, prQ, fun η _ => (prQ_deriv η).hasDerivWithinAt,
    fun η hη => by rw [← prG_ode η hη]; exact (prQ_deriv η).hasDerivWithinAt, by simp [prG],
    prP_zero, prQ_zero, prP_lim, prQ_pos, pr_decay, ?_⟩
  simp

/-- The Falkner–Skan equation is needed in `fs_separation_not_printed_value`: the profile above with
`f = ∫ p` meets every other condition at the printed `β`. -/
theorem fs_separation_not_printed_value_h3 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_not_printed_value 3 := by
  refine ⟨-(1988376 / 10000000), prF, prP, prQ, fun η _ => (prF_deriv η).hasDerivWithinAt,
    fun η _ => (prP_deriv η).hasDerivWithinAt, by simp [prF],
    prP_zero, prQ_zero, prP_lim, prQ_pos, pr_decay, ?_⟩
  simp

end Checked.Trust.NCP
