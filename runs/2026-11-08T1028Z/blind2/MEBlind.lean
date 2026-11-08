import Mathlib

namespace Blind.MonotoneExists

open Filter Set Topology

/-- `f` solves `f''' + c f f'' + 1 - (f')² = 0` on `[0,∞)` with `f(0)=0`, `f'(0)=0`, `f' → 1`;
derivatives are one-sided at 0 (`derivWithin` on `Ici 0`), regularity `C^n` on `Ici 0`. -/
def IsSol (n : WithTop ℕ∞) (c : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ n f (Ici 0) ∧
  (∀ x ∈ Ici (0:ℝ),
    derivWithin (derivWithin (derivWithin f (Ici 0)) (Ici 0)) (Ici 0) x
      + c * f x * derivWithin (derivWithin f (Ici 0)) (Ici 0) x + 1
      - (derivWithin f (Ici 0) x) ^ 2 = 0) ∧
  f 0 = 0 ∧ derivWithin f (Ici 0) 0 = 0 ∧
  Tendsto (derivWithin f (Ici 0)) atTop (𝓝 1)

/-- Hiemenz: a `C^∞` solution with `f'' > 0` and `f''(0) ∈ (1.2325876568, 1.2325876569)`. -/
theorem hiemenz_exists_blind :
    ∃ f : ℝ → ℝ, IsSol ⊤ 1 f ∧
      (∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin f (Ici 0)) (Ici 0) x) ∧
      (1.2325876568 : ℝ) < derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
      derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 < (1.2325876569 : ℝ) := by
  sorry

/-- Homann: a `C^∞` solution with `f'' > 0` and `f''(0) ∈ (1.3119376938, 1.3119376939)`. -/
theorem homann_exists_blind :
    ∃ f : ℝ → ℝ, IsSol ⊤ 2 f ∧
      (∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin f (Ici 0)) (Ici 0) x) ∧
      (1.3119376938 : ℝ) < derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 ∧
      derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 < (1.3119376939 : ℝ) := by
  sorry

/-- Hiemenz: two `C^3` solutions with `f'' > 0` on `[0,∞)` have equal wall shear. -/
theorem hiemenz_unique_blind (f g : ℝ → ℝ) (hf : IsSol 3 1 f) (hg : IsSol 3 1 g)
    (hf2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin f (Ici 0)) (Ici 0) x)
    (hg2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin g (Ici 0)) (Ici 0) x) :
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 =
      derivWithin (derivWithin g (Ici 0)) (Ici 0) 0 := by
  sorry

/-- Homann: two `C^3` solutions with `f'' > 0` on `[0,∞)` have equal wall shear. -/
theorem homann_unique_blind (f g : ℝ → ℝ) (hf : IsSol 3 2 f) (hg : IsSol 3 2 g)
    (hf2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin f (Ici 0)) (Ici 0) x)
    (hg2 : ∀ x ∈ Ici (0:ℝ), 0 < derivWithin (derivWithin g (Ici 0)) (Ici 0) x) :
    derivWithin (derivWithin f (Ici 0)) (Ici 0) 0 =
      derivWithin (derivWithin g (Ici 0)) (Ici 0) 0 := by
  sorry

end Blind.MonotoneExists
