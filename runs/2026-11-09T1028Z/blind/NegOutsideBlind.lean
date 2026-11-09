import Mathlib

namespace Blind.NegOutside

open Set Filter Topology

/-- First, second, third one-sided derivatives on `[0,∞)`. -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- `f` solves Falkner–Skan with parameter `β` on `[0,∞)` with the stated boundary conditions. -/
def IsSol (β : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici 0) ∧
  (∀ η ∈ Ici (0:ℝ), d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0) ∧
  f 0 = 0 ∧ d1 f 0 = 0 ∧
  Tendsto (d1 f) atTop (𝓝 1)

/-- Positivity of `f''` and `0 ≤ f' ≤ 1` on the half-line. -/
def Monotone' (f : ℝ → ℝ) : Prop :=
  ∀ η ∈ Ici (0:ℝ), 0 < d2 f η ∧ 0 ≤ d1 f η ∧ d1 f η ≤ 1

/-- The property "for every `M`, eventually `M (1 - f') ≤ f''`". -/
def DominatesAll (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η

theorem two_outside :
    ∃ f g : ℝ → ℝ,
      IsSol (-1/10) f ∧ IsSol (-1/10) g ∧
      Monotone' f ∧ Monotone' g ∧
      ¬ DominatesAll f ∧ ¬ DominatesAll g ∧
      d2 f 0 ≠ d2 g 0 := by
  sorry

end Blind.NegOutside
