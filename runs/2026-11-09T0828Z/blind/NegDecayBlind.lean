import Mathlib

namespace Blind.NegDecay

open Filter Topology

/-- Falkner–Skan solution data: `f1 = f'`, `f2 = f''`, `f3 = f'''`, derivatives within `[0,∞)`,
ODE `f''' + f f'' + β(1 - (f')²) = 0` at every `η ≥ 0`, wall conditions `f 0 = 0`, `f' 0 = 0`,
and `f' → 1` at infinity. -/
def IsSolution (β : ℝ) (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ η : ℝ, 0 ≤ η → HasDerivWithinAt f (f1 η) (Set.Ici 0) η) ∧
  (∀ η : ℝ, 0 ≤ η → HasDerivWithinAt f1 (f2 η) (Set.Ici 0) η) ∧
  (∀ η : ℝ, 0 ≤ η → HasDerivWithinAt f2 (f3 η) (Set.Ici 0) η) ∧
  (∀ η : ℝ, 0 ≤ η → f3 η + f η * f2 η + β * (1 - (f1 η) ^ 2) = 0) ∧
  f 0 = 0 ∧ f1 0 = 0 ∧
  Tendsto f1 atTop (𝓝 1)

/-- (M): `f'' > 0` for every `η ≥ 0`. -/
def IsMonotone (f2 : ℝ → ℝ) : Prop := ∀ η : ℝ, 0 ≤ η → 0 < f2 η

/-- (E): for every real `M`, `f'' η ≥ M * (1 - f' η)` for all sufficiently large `η`. -/
def FastDecay (f1 f2 : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ η : ℝ, R ≤ η → M * (1 - f1 η) ≤ f2 η

/-- For `β < 0`, if one solution satisfies (M) and (E) and another satisfies (M), then the wall
shear `f''(0)` of the second is at most that of the first. -/
theorem max_wall_shear (β : ℝ) (hβ : β < 0)
    (f f1 f2 f3 : ℝ → ℝ) (g g1 g2 g3 : ℝ → ℝ)
    (hf : IsSolution β f f1 f2 f3) (hfM : IsMonotone f2) (hfE : FastDecay f1 f2)
    (hg : IsSolution β g g1 g2 g3) (hgM : IsMonotone g2) :
    g2 0 ≤ f2 0 := by
  sorry

/-- For `β < 0`, any two solutions both satisfying (M) and (E) agree, together with their first and
second derivatives, at every `η ≥ 0`. -/
theorem unique_in_class (β : ℝ) (hβ : β < 0)
    (f f1 f2 f3 : ℝ → ℝ) (g g1 g2 g3 : ℝ → ℝ)
    (hf : IsSolution β f f1 f2 f3) (hfM : IsMonotone f2) (hfE : FastDecay f1 f2)
    (hg : IsSolution β g g1 g2 g3) (hgM : IsMonotone g2) (hgE : FastDecay g1 g2) :
    ∀ η : ℝ, 0 ≤ η → f η = g η ∧ f1 η = g1 η ∧ f2 η = g2 η := by
  sorry

end Blind.NegDecay
