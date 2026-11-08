import Mathlib

/-!
# Falkner–Skan rows: the blind restatement (run 2026-11-08T0828Z)

Copied verbatim (module doc added) from `runs/2026-11-08T0828Z/blind/FSBlind.lean`, written by a
blind restater (Sonnet) from the claims in words: a solution is one function with iterated
`derivWithin` on `Ici 0`, differentiable within `Ici 0` three times, the equation pointwise.
-/

namespace Blind.FalknerSkan

open Set Filter Topology

/-- `f` solves `f''' + f f'' + β (1 - f'^2) = 0` on `[0,∞)` with `f(0)=0`, `f'(0)=0`,
`f'(η) → 1`. Derivatives are taken within `[0,∞)`. -/
def IsSolution (β : ℝ) (f : ℝ → ℝ) : Prop :=
  let f1 := derivWithin f (Ici 0)
  let f2 := derivWithin f1 (Ici 0)
  let f3 := derivWithin f2 (Ici 0)
  (∀ x ∈ Ici (0:ℝ), DifferentiableWithinAt ℝ f (Ici 0) x) ∧
  (∀ x ∈ Ici (0:ℝ), DifferentiableWithinAt ℝ f1 (Ici 0) x) ∧
  (∀ x ∈ Ici (0:ℝ), DifferentiableWithinAt ℝ f2 (Ici 0) x) ∧
  (∀ x ∈ Ici (0:ℝ), f3 x + f x * f2 x + β * (1 - (f1 x)^2) = 0) ∧
  f 0 = 0 ∧ f1 0 = 0 ∧
  Tendsto f1 atTop (𝓝 1)

theorem claimA :
    ∃ f : ℝ → ℝ, IsSolution (1/2) f ∧
      (0.927680039 : ℝ) < derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
      derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 < (0.927680040 : ℝ) := by
  sorry

theorem claimB :
    ∀ f : ℝ → ℝ, IsSolution 0 f →
      (0.4695999883610 : ℝ) ≤ derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
      derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ≤ (0.4695999883611 : ℝ) := by
  sorry

end Blind.FalknerSkan
