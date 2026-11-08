import Mathlib

namespace Blind.FSTenth

open Set Filter Topology

/-- `f` solves Falkner–Skan with `β = 1/10` on `[0,∞)`; `f1 f2 f3` are its first three
derivatives (one-sided at `0`, given explicitly to avoid junk values of `deriv`). -/
structure IsSol (f f1 f2 f3 : ℝ → ℝ) : Prop where
  d0 : ∀ η, 0 ≤ η → HasDerivWithinAt f (f1 η) (Ici 0) η
  d1 : ∀ η, 0 ≤ η → HasDerivWithinAt f1 (f2 η) (Ici 0) η
  d2 : ∀ η, 0 ≤ η → HasDerivWithinAt f2 (f3 η) (Ici 0) η
  ode : ∀ η, 0 ≤ η → f3 η + f η * f2 η + (1/10 : ℝ) * (1 - (f1 η)^2) = 0
  bc0 : f 0 = 0
  bc1 : f1 0 = 0
  bcInf : Tendsto f1 atTop (𝓝 1)

theorem fs_W (f f1 f2 f3 : ℝ → ℝ) (h : IsSol f f1 f2 f3)
    (hb : ∀ η, 0 ≤ η → -1 ≤ f1 η ∧ f1 η ≤ 1) :
    (0.5870352191 : ℝ) < f2 0 ∧ f2 0 < 0.5870352193 := by
  sorry

theorem fs_U (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (h : IsSol f f1 f2 f3) (hg : IsSol g g1 g2 g3)
    (hb : ∀ η, 0 ≤ η → -1 ≤ f1 η ∧ f1 η ≤ 1)
    (hgb : ∀ η, 0 ≤ η → -1 ≤ g1 η ∧ g1 η ≤ 1) :
    ∀ η, 0 ≤ η → f η = g η ∧ f1 η = g1 η ∧ f2 η = g2 η := by
  sorry

theorem fs_E : ∃ f f1 f2 f3 : ℝ → ℝ, IsSol f f1 f2 f3 ∧
    (∀ η, 0 ≤ η → 0 ≤ f1 η ∧ f1 η < 1) ∧
    (0.5870352191 : ℝ) < f2 0 ∧ f2 0 < 0.5870352193 := by
  sorry

end Blind.FSTenth
