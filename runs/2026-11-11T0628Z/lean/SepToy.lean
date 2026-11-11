import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationEqual
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Toy profile for the separation pair: `p = 1 − (1 + η²) e^{−η²}`, `q = p' = 2η³ e^{−η²}`. It starts at
`p = q = 0`, tends to `1`, has `q > 0` beyond the wall and `q/(1 − p) = 2η³/(1 + η²) → ∞`, but it solves
no Falkner–Skan equation together with `f = ∫ p`.
-/

open Set Filter Topology

namespace Checked.Trust.NCD

noncomputable def toyP (η : ℝ) : ℝ := 1 - (1 + η ^ 2) * Real.exp (-η ^ 2)
noncomputable def toyQ (η : ℝ) : ℝ := 2 * η ^ 3 * Real.exp (-η ^ 2)
noncomputable def toyQ' (η : ℝ) : ℝ := (6 * η ^ 2 - 4 * η ^ 4) * Real.exp (-η ^ 2)

theorem toy_hasDerivAt_exp (η : ℝ) :
    HasDerivAt (fun η : ℝ => Real.exp (-η ^ 2)) (-(2 * η) * Real.exp (-η ^ 2)) η := by
  have := ((hasDerivAt_pow 2 η).neg).exp
  convert this using 1; simp only [Pi.neg_apply]; push_cast; ring

theorem toyP_deriv (η : ℝ) : HasDerivAt toyP (toyQ η) η := by
  have h := ((hasDerivAt_pow 2 η).const_add 1).mul (toy_hasDerivAt_exp η)
  have := h.const_sub 1
  unfold toyP toyQ
  convert this using 1; push_cast; ring

theorem toyQ_deriv (η : ℝ) : HasDerivAt toyQ (toyQ' η) η := by
  have h := ((hasDerivAt_pow 3 η).const_mul 2).mul (toy_hasDerivAt_exp η)
  unfold toyQ toyQ'
  convert h using 1; push_cast; ring

theorem toyP_zero : toyP 0 = 0 := by simp [toyP]
theorem toyQ_zero : toyQ 0 = 0 := by simp [toyQ]

theorem toyQ_pos : ∀ η ∈ Ioi (0 : ℝ), 0 < toyQ η := by
  intro η hη; unfold toyQ; have : (0 : ℝ) < η := hη; positivity

theorem toyP_lim : Tendsto toyP atTop (𝓝 1) := by
  have hu : Tendsto (fun η : ℝ => η ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hu
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have := (h0.add h1).const_sub 1
  simp only [add_zero, sub_zero] at this
  refine this.congr fun η => ?_
  simp only [Function.comp, toyP, pow_zero, pow_one]; ring

theorem toy_decay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - toyP η) ≤ toyQ η := by
  intro M
  filter_upwards [eventually_ge_atTop (|M| + 1)] with η hη
  have h1 : (1 : ℝ) ≤ η := by linarith [abs_nonneg M]
  have hM : |M| ≤ η := by linarith
  have he := Real.exp_pos (-η ^ 2)
  have key : M * (1 + η ^ 2) ≤ 2 * η ^ 3 := by
    calc M * (1 + η ^ 2) ≤ |M| * (1 + η ^ 2) := by
          apply mul_le_mul_of_nonneg_right (le_abs_self M); positivity
      _ ≤ η * (2 * η ^ 2) := by
          apply mul_le_mul hM (by nlinarith) (by positivity) (by linarith)
      _ = 2 * η ^ 3 := by ring
  have : 1 - toyP η = (1 + η ^ 2) * Real.exp (-η ^ 2) := by unfold toyP; ring
  rw [this]; unfold toyQ
  nlinarith [mul_le_mul_of_nonneg_right key he.le]

/-- `f = ∫₀^η p`, so that `f' = p` and `f(0) = 0`. -/
noncomputable def toyF (η : ℝ) : ℝ := ∫ s in (0 : ℝ)..η, toyP s

theorem toyP_cont : Continuous toyP := by unfold toyP; fun_prop

theorem toyF_deriv (η : ℝ) : HasDerivAt toyF (toyP η) η :=
  (toyP_cont.integral_hasStrictDerivAt 0 η).hasDerivAt

/-- `f` chosen so that `q' = −f q` (the Falkner–Skan equation with `β = 0`), `f = −q'/q`, `f(0) = 0`. -/
noncomputable def toyG (η : ℝ) : ℝ := if η = 0 then 0 else -(toyQ' η / toyQ η)

theorem toyG_ode (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) :
    toyQ' η = -(toyG η * toyQ η) - 0 * (1 - toyP η ^ 2) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ η from hη) with h | h
  · subst h; simp [toyQ', toyG]
  · have hq := toyQ_pos η h
    simp only [toyG, h.ne', ite_false]
    field_simp
    ring

open Checked.FalknerSkan in
/-- `f' = p` is needed for the first profile in `fs_separation_equal`: the toy profile with `f = −q'/q`
satisfies `q' = −f q` (`β = 0`), every boundary and decay condition, but `0` is not the separation value. -/
theorem fs_separation_equal_h1 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 1 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨0, β, toyG, toyP, toyQ, f, p, q, fun η _ => (toyP_deriv η).hasDerivWithinAt,
    fun η hη => by rw [← toyG_ode η hη]; exact (toyQ_deriv η).hasDerivWithinAt, by simp [toyG],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec, ?_⟩
  intro h; have := hβ.2; linarith

open Checked.FalknerSkan in
theorem fs_separation_equal_h10 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 10 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨β, 0, f, p, q, toyG, toyP, toyQ, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec,
    fun η _ => (toyP_deriv η).hasDerivWithinAt,
    fun η hη => by rw [← toyG_ode η hη]; exact (toyQ_deriv η).hasDerivWithinAt, by simp [toyG],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, ?_⟩
  intro h; have := hβ.2; linarith

open Checked.FalknerSkan in
/-- The Falkner–Skan equation is needed for the first profile in `fs_separation_equal`: the toy
profile with `f = ∫ p` meets every other condition at `β = 0`, which is not the separation value. -/
theorem fs_separation_equal_h3 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 3 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨0, β, toyF, toyP, toyQ, f, p, q, fun η _ => (toyF_deriv η).hasDerivWithinAt,
    fun η _ => (toyP_deriv η).hasDerivWithinAt, by simp [toyF],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec, ?_⟩
  intro h; have := hβ.2; linarith

open Checked.FalknerSkan in
theorem fs_separation_equal_h12 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 12 := by
  obtain ⟨β, hβ, f, p, q, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec⟩ :=
    Separation.fs_separation_exists
  refine ⟨β, 0, f, p, q, toyF, toyP, toyQ, hf, hp, hq, hf0, hp0, hq0, hlim, hpos, hdec,
    fun η _ => (toyF_deriv η).hasDerivWithinAt,
    fun η _ => (toyP_deriv η).hasDerivWithinAt, by simp [toyF],
    toyP_zero, toyQ_zero, toyP_lim, toyQ_pos, toy_decay, ?_⟩
  intro h; have := hβ.2; linarith

end Checked.Trust.NCD
