import Mathlib

namespace Blind.NegReversed

open Set Filter Topology

/-- One-sided derivative on the half-line `[0, ∞)`. -/
noncomputable def D (g : ℝ → ℝ) : ℝ → ℝ := derivWithin g (Ici 0)

/-- Falkner–Skan pressure-gradient parameter. -/
noncomputable def β : ℝ := -1 / 10

/-- `f` solves the Falkner–Skan BVP with parameter `β = -1/10`, has `-1 ≤ f' ≤ 1`
on `[0,∞)`, and the growth property
`∀ M, ∀ᶠ η, M * (1 - f' η) ≤ f'' η`. -/
structure IsSol (f : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 3 f (Ici 0)
  ode : ∀ η ∈ Ici (0 : ℝ), D (D (D f)) η + f η * D (D f) η + β * (1 - (D f η) ^ 2) = 0
  f0 : f 0 = 0
  f'0 : D f 0 = 0
  f'_lim : Tendsto (D f) atTop (𝓝 1)
  bounds : ∀ η ∈ Ici (0 : ℝ), -1 ≤ D f η ∧ D f η ≤ 1
  decay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - D f η) ≤ D (D f) η

theorem reversed :
    ∃ f : ℝ → ℝ, IsSol f ∧
      (-1405462131 / 10000000000 : ℝ) < D (D f) 0 ∧
      D (D f) 0 < (-1405462129 / 10000000000 : ℝ) := by
  sorry

theorem two_decay :
    ∃ f g : ℝ → ℝ, IsSol f ∧ IsSol g ∧ D (D f) 0 ≠ D (D g) 0 := by
  sorry

end Blind.NegReversed
