import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationPrinted
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Hypothesis necessity witnesses, the printed separation value (trust track T2b, run 2026-11-11T0828Z)

Profile `p = 1 − e^{−k η²}`, `q = p' = 2 k η e^{−k η²}` with `k = 1988376 / 20000000`, so that `q'(0) = 2k`
is minus the printed parameter: it starts at `p = q = 0`, tends to `1`, has `q > 0` beyond the wall and
`q / (1 − p) = 2 k η → ∞`. With `f = ∫ p` it solves no Falkner–Skan equation (the equation hypothesis
is needed); with `f = −(q' + c(1 − p²)) / q` (`c` the printed parameter, junk value `0` at the wall, where the
equation holds because `q'(0) = −c`) it solves the equation but `f' ≠ p` (the hypothesis `f' = p` is
needed). In both cases β is the printed parameter, so the conclusion (β below it) is false.
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
  have h1 : HasDerivAt (fun x : ℝ => -(kP * x ^ 2)) (-(2 * kP * η)) η := by
    convert (hasDerivAt_pow 2 η).const_mul (-kP) using 1
    all_goals first
      | (funext x; ring)
      | ring
      | (norm_num; done)
      | (norm_num; ring)
      | (simp; ring)
  refine h1.exp.congr_deriv ?_
  first
    | ring
    | (beta_reduce; ring)

theorem prP_deriv (η : ℝ) : HasDerivAt prP (prQ η) η := by
  have := (pr_exp_deriv η).const_sub 1
  unfold prP prQ; convert this using 1; ring

theorem prQ_deriv (η : ℝ) : HasDerivAt prQ (prQ' η) η := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * kP * x) (2 * kP) η := by
    simpa using (hasDerivAt_id η).const_mul (2 * kP)
  have h := h1.mul (pr_exp_deriv η)
  have e : prQ = (fun x : ℝ => 2 * kP * x) * (fun x : ℝ => Real.exp (-(kP * x ^ 2))) := by
    funext x; simp only [prQ, Pi.mul_apply]
  rw [e]
  refine h.congr_deriv ?_
  unfold prQ'
  ring

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

/-- `f' = p` is needed in `fs_separation_below_printed`: the profile above with `f = −(q' + c(1 − p²))/q`
solves the equation at the printed `β = c`, meets every boundary and decay condition, and β equals `c`. -/
theorem fs_separation_below_printed_h1 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 1 := by
  refine ⟨-(1988376 / 10000000), prG, prP, prQ, fun η _ => (prP_deriv η).hasDerivWithinAt,
    fun η hη => by rw [← prG_ode η hη]; exact (prQ_deriv η).hasDerivWithinAt, by simp [prG],
    prP_zero, prQ_zero, prP_lim, prQ_pos, pr_decay, ?_⟩
  simp

/-- The Falkner–Skan equation is needed in `fs_separation_below_printed`: the profile above with
`f = ∫ p` meets every other condition at the printed `β`. -/
theorem fs_separation_below_printed_h3 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 3 := by
  refine ⟨-(1988376 / 10000000), prF, prP, prQ, fun η _ => (prF_deriv η).hasDerivWithinAt,
    fun η _ => (prP_deriv η).hasDerivWithinAt, by simp [prF],
    prP_zero, prQ_zero, prP_lim, prQ_pos, pr_decay, ?_⟩
  simp

/- Witness for hypothesis 2 (p' = q) of `fs_separation_below_printed` 
p = min η 1, f = ∫ p, and q the solution of the linear equation q' = −f q − β(1 − p²) with q(0) = 0 at the
printed β: q = e^{−F} ∫₀^η e^{F} (−β)(1 − p²), F = ∫ f. The forcing vanishes for η ≥ 1, so 1 − p = 0 there and
the decay condition holds; q > 0 beyond the wall; but q is not p' (p' = 0 for η > 1, q > 0). -/

noncomputable def p2 (η : ℝ) : ℝ := min η 1
noncomputable def f2 (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, p2 s
noncomputable def F2 (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, f2 s
noncomputable def g2 (s : ℝ) : ℝ := Real.exp (F2 s) * (1988376 / 10000000 * (1 - p2 s ^ 2))
noncomputable def G2 (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, g2 s
noncomputable def q2 (η : ℝ) : ℝ := Real.exp (-F2 η) * G2 η

theorem p2_cont : Continuous p2 := continuous_id.min continuous_const

theorem f2_deriv (η : ℝ) : HasDerivAt f2 (p2 η) η :=
  (p2_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem f2_cont : Continuous f2 :=
  continuous_iff_continuousAt.2 fun η => (f2_deriv η).continuousAt

theorem F2_deriv (η : ℝ) : HasDerivAt F2 (f2 η) η :=
  (f2_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem F2_cont : Continuous F2 :=
  continuous_iff_continuousAt.2 fun η => (F2_deriv η).continuousAt

theorem g2_cont : Continuous g2 :=
  (Real.continuous_exp.comp F2_cont).mul
    (continuous_const.mul (continuous_const.sub (p2_cont.pow 2)))

theorem G2_deriv (η : ℝ) : HasDerivAt G2 (g2 η) η :=
  (g2_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

theorem q2_deriv (η : ℝ) :
    HasDerivAt q2 (-(f2 η * q2 η) - -(1988376 / 10000000 : ℝ) * (1 - p2 η ^ 2)) η := by
  have h := (((F2_deriv η).neg).exp).mul (G2_deriv η)
  have e : Real.exp (-F2 η) * Real.exp (F2 η) = 1 := by rw [← Real.exp_add]; simp
  refine h.congr_deriv ?_
  unfold g2 q2
  try simp only [Pi.neg_apply]
  linear_combination (1988376 / 10000000 * (1 - p2 η ^ 2)) * e

theorem g2_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ g2 s := by
  have h1 : p2 s ≤ 1 := min_le_right _ _
  have h0 : 0 ≤ p2 s := le_min hs zero_le_one
  have : 0 ≤ 1 - p2 s ^ 2 := by nlinarith
  unfold g2; positivity

theorem G2_pos {η : ℝ} (hη : 0 < η) : 0 < G2 η := by
  set m := min η (1 / 2) with hm
  have hm0 : 0 < m := lt_min hη (by norm_num)
  have hmη : m ≤ η := min_le_left _ _
  have hm1 : m ≤ 1 / 2 := min_le_right _ _
  have i1 : IntervalIntegrable g2 MeasureTheory.volume 0 m := g2_cont.intervalIntegrable _ _
  have i2 : IntervalIntegrable g2 MeasureTheory.volume m η := g2_cont.intervalIntegrable _ _
  have a : 0 < ∫ s in (0 : ℝ)..m, g2 s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on i1 (fun s hs => ?_) hm0
    have hs1 : s < 1 := by linarith [hs.2]
    have hp : p2 s = s := min_eq_left hs1.le
    have : 0 < 1 - p2 s ^ 2 := by rw [hp]; nlinarith [hs.1]
    unfold g2; positivity
  have b : 0 ≤ ∫ s in m..η, g2 s :=
    intervalIntegral.integral_nonneg hmη (fun s hs => g2_nonneg (hm0.le.trans hs.1))
  have := intervalIntegral.integral_add_adjacent_intervals i1 i2
  unfold G2; rw [← this]; linarith

theorem q2_pos : ∀ η ∈ Ioi (0 : ℝ), 0 < q2 η := by
  intro η hη; unfold q2; exact mul_pos (Real.exp_pos _) (G2_pos hη)

theorem p2_lim : Tendsto p2 atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with η hη
    exact (min_eq_right hη).symm)

theorem p2_decay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p2 η) ≤ q2 η := by
  intro M
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with η hη
  have hp : p2 η = 1 := min_eq_right hη
  rw [hp, sub_self, mul_zero]
  exact (q2_pos η (by simp only [mem_Ioi]; linarith)).le

/-- `p' = q` is needed in `fs_separation_below_printed`: with p = min(η, 1), f = ∫ p and q the solution
of the equation's linear q-part at the printed β, every other condition holds and β is the printed value. -/
theorem fs_separation_below_printed_h2 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 2 := by
  refine ⟨-(1988376 / 10000000), f2, p2, q2, fun η _ => (f2_deriv η).hasDerivWithinAt,
    fun η _ => (q2_deriv η).hasDerivWithinAt, by simp [f2], by simp [p2], by simp [q2, G2],
    p2_lim, q2_pos, p2_decay, ?_⟩
  simp

end Checked.Trust.NCP
