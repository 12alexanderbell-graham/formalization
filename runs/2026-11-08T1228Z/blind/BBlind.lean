import Mathlib

namespace Blind.Bounded

open Set Filter Topology

/-- one-sided derivatives on [0,∞) -/
noncomputable def D1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
noncomputable def D2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (D1 f) (Ici 0)
noncomputable def D3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (D2 f) (Ici 0)

/-- BVP f''' + c f f'' + 1 - (f')^2 = 0 on [0,∞), f(0)=0, f'(0)=0, f' → 1.
c = 1 Hiemenz, c = 2 Homann. -/
def IsSol (c : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici 0) ∧
  (∀ η, 0 ≤ η → D3 f η + c * f η * D2 f η + 1 - (D1 f η)^2 = 0) ∧
  f 0 = 0 ∧ D1 f 0 = 0 ∧ Tendsto (D1 f) atTop (𝓝 1)

def Bdd (f : ℝ → ℝ) : Prop := ∀ η, 0 ≤ η → -1 ≤ D1 f η ∧ D1 f η ≤ 1

-- Hiemenz
theorem hiemenz_W (f : ℝ → ℝ) (h : IsSol 1 f) (hb : Bdd f) :
    1.2325876568 < D2 f 0 ∧ D2 f 0 < 1.2325876569 := sorry

theorem hiemenz_U (f g : ℝ → ℝ) (hf : IsSol 1 f) (hg : IsSol 1 g)
    (hfb : Bdd f) (hgb : Bdd g) : EqOn f g (Ici 0) := sorry

theorem hiemenz_E : ∃ f : ℝ → ℝ, IsSol 1 f ∧ (∀ η, 0 ≤ η → 0 ≤ D1 f η ∧ D1 f η < 1) ∧
    1.2325876568 < D2 f 0 ∧ D2 f 0 < 1.2325876569 := sorry

-- Homann
theorem homann_W (f : ℝ → ℝ) (h : IsSol 2 f) (hb : Bdd f) :
    1.3119376938 < D2 f 0 ∧ D2 f 0 < 1.3119376939 := sorry

theorem homann_U (f g : ℝ → ℝ) (hf : IsSol 2 f) (hg : IsSol 2 g)
    (hfb : Bdd f) (hgb : Bdd g) : EqOn f g (Ici 0) := sorry

theorem homann_E : ∃ f : ℝ → ℝ, IsSol 2 f ∧ (∀ η, 0 ≤ η → 0 ≤ D1 f η ∧ D1 f η < 1) ∧
    1.3119376938 < D2 f 0 ∧ D2 f 0 < 1.3119376939 := sorry

end Blind.Bounded
