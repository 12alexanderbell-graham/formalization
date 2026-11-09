import Mathlib

namespace Blind.NegWindow

open Set Filter Topology

/-- First, second, third derivatives of `f` on the half-line `[0,∞)` (one-sided at 0). -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- `f` solves the Falkner–Skan boundary-value problem with parameter `β`. -/
structure IsSolution (β : ℝ) (f : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 3 f (Ici 0)
  ode : ∀ η, 0 ≤ η → d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0
  f0 : f 0 = 0
  f'0 : d1 f 0 = 0
  limit : Tendsto (d1 f) atTop (𝓝 1)

theorem window (f : ℝ → ℝ) (hf : IsSolution (-1/10) f)
    (hpos : ∀ η, 0 ≤ η → 0 < d2 f η)
    (hdecay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η) :
    (3192697598 / 10 ^ 10 : ℝ) < d2 f 0 ∧ d2 f 0 < 3192697599 / 10 ^ 10 := by
  sorry

theorem monotone_lt (f : ℝ → ℝ) (hf : IsSolution (-1/10) f)
    (hpos : ∀ η, 0 ≤ η → 0 < d2 f η) :
    d2 f 0 < 3192697599 / 10 ^ 10 := by
  sorry

end Blind.NegWindow
