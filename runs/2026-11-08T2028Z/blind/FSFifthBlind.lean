import Mathlib

namespace Blind.FSFifth

open Filter Topology Set

/-- `IsSol f f1 f2 f3`: f, f1 = f', f2 = f'', f3 = f''' are explicit functions with
one-sided (within `Ici 0`) derivatives at every η ≥ 0, satisfying the Falkner–Skan ODE
with β = 1/5 and the boundary conditions. -/
def IsSol (f f1 f2 f3 : ℝ → ℝ) : Prop :=
  (∀ η ∈ Ici (0:ℝ), HasDerivWithinAt f (f1 η) (Ici 0) η) ∧
  (∀ η ∈ Ici (0:ℝ), HasDerivWithinAt f1 (f2 η) (Ici 0) η) ∧
  (∀ η ∈ Ici (0:ℝ), HasDerivWithinAt f2 (f3 η) (Ici 0) η) ∧
  (∀ η ∈ Ici (0:ℝ), f3 η + f η * f2 η + (1/5 : ℝ) * (1 - (f1 η)^2) = 0) ∧
  f 0 = 0 ∧ f1 0 = 0 ∧ Tendsto f1 atTop (𝓝 1)

/-- velocity profile bounded in [-1,1] on [0,∞) -/
def Bdd (f1 : ℝ → ℝ) : Prop := ∀ η, 0 ≤ η → -1 ≤ f1 η ∧ f1 η ≤ 1

theorem fs_W (f f1 f2 f3 : ℝ → ℝ) (h : IsSol f f1 f2 f3) (hb : Bdd f1) :
    (0.6867081809 : ℝ) < f2 0 ∧ f2 0 < 0.6867081811 := by
  sorry

theorem fs_U (f f1 f2 f3 g g1 g2 g3 : ℝ → ℝ)
    (h : IsSol f f1 f2 f3) (hb : Bdd f1) (k : IsSol g g1 g2 g3) (kb : Bdd g1) :
    ∀ η, 0 ≤ η → f η = g η ∧ f1 η = g1 η ∧ f2 η = g2 η := by
  sorry

theorem fs_E : ∃ f f1 f2 f3 : ℝ → ℝ, IsSol f f1 f2 f3 ∧
    (∀ η, 0 ≤ η → 0 ≤ f1 η ∧ f1 η < 1) ∧
    (0.6867081809 : ℝ) < f2 0 ∧ f2 0 < 0.6867081811 := by
  sorry

end Blind.FSFifth
