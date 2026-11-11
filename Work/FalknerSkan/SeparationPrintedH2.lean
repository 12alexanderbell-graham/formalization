import Checked.Trust.NonVacuity
import Checked.FalknerSkan.SeparationPrinted
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Necessity witness for hypothesis 2 of `Checked.FalknerSkan.SeparationPrinted.fs_separation_not_printed_value`
(run 2026-11-11T0828Z), compiled in Work first; moves to `Checked/Trust/NecessityE.lean` once green. -/

open Set Filter Topology

namespace Work.Trust.NCPH2

/- Witness for hypothesis 2 (p' = q) of `fs_separation_not_printed_value` (append to NecessityE, namespace NCP).
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

/-- `p' = q` is needed in `fs_separation_not_printed_value`: with p = min(η, 1), f = ∫ p and q the solution
of the equation's linear q-part at the printed β, every other condition holds and β is the printed value. -/
theorem fs_separation_not_printed_value_h2 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_not_printed_value 2 := by
  refine ⟨-(1988376 / 10000000), f2, p2, q2, fun η _ => (f2_deriv η).hasDerivWithinAt,
    fun η _ => (q2_deriv η).hasDerivWithinAt, by simp [f2], by simp [p2], by simp [q2, G2],
    p2_lim, q2_pos, p2_decay, ?_⟩
  simp

end Work.Trust.NCPH2
