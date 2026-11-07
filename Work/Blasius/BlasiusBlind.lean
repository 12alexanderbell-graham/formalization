import Mathlib

/-! Verbatim copy of the blind restater's file `runs/2026-11-07T1228Z/blind/BlasiusBlind.lean`
(run 2026-11-07T1228Z, Sonnet, written from the informal claim without access to the program's
statement). -/

namespace Blind.Blasius

open Set Filter Topology

/-- `f` solves the Blasius boundary-value problem on `[0, ∞)`.
Derivatives are taken *within* `Ici 0` (one-sided at the wall), so no junk values
arise: `ContDiffOn ℝ 3 f (Ici 0)` makes `f, f', f'', f'''` genuinely differentiable
on `[0,∞)` (unique differentiability of `Ici 0` makes `derivWithin` the true derivative). -/
def IsBlasiusSolution (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici (0 : ℝ)) ∧
  (∀ η ∈ Ici (0 : ℝ),
    derivWithin (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) η
      + (1 / 2) * f η * derivWithin (derivWithin f (Ici 0)) (Ici 0) η = 0) ∧
  f 0 = 0 ∧
  derivWithin f (Ici 0) 0 = 0 ∧
  Tendsto (derivWithin f (Ici 0)) atTop (𝓝 1)

/-- Wall shear bound: every `C³`-on-`[0,∞)` solution has
`f''(0) ∈ [0.33205733621519, 0.33205733621520]`.
Choices: regularity only `ContDiffOn ℝ 3 f (Ici 0)` (the minimum for the ODE to make
sense classically), one-sided derivatives at `η = 0` via `derivWithin`, decimals as
exact rationals. The claim is true because the solution with `f' → 1` is unique. -/
theorem wall_shear_bounds (f : ℝ → ℝ) (hf : IsBlasiusSolution f) :
    (0.33205733621519 : ℝ) ≤ derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ≤ (0.33205733621520 : ℝ) := by
  sorry

/-- Existence of a solution of the Blasius boundary-value problem (same notion as above). -/
theorem exists_blasius_solution : ∃ f : ℝ → ℝ, IsBlasiusSolution f := by
  sorry

end Blind.Blasius
