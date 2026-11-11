import Mathlib

open Set Filter

namespace Neg1988Blind

/-- The wall-shear parameter. -/
noncomputable def β : ℝ := -0.1988

/-- First derivative on the half-line `[0, ∞)`. -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
/-- Second derivative on the half-line. -/
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
/-- Third derivative on the half-line. -/
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- `f` solves the Falkner–Skan boundary value problem on `η ≥ 0`
with `β = -0.1988`, `f 0 = 0`, `f' 0 = 0`, `f' → 1`. -/
structure IsSolution (f : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 3 f (Ici 0)
  ode : ∀ η ∈ Ici (0 : ℝ),
    d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0
  f_zero : f 0 = 0
  f'_zero : d1 f 0 = 0
  f'_tendsto : Tendsto (d1 f) atTop (nhds 1)

/-- Attached: `f'' > 0` for every `η ≥ 0`. -/
def Attached (f : ℝ → ℝ) : Prop := ∀ η ∈ Ici (0 : ℝ), 0 < d2 f η

/-- Faster than any exponential rate: for every real `M`, eventually
`M * (1 - f') ≤ f''`. -/
def SuperExpApproach (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η

theorem blind_neg1988_window (f : ℝ → ℝ) (hf : IsSolution f)
    (hatt : Attached f) (hfast : SuperExpApproach f) :
    (0.0052181 : ℝ) < d2 f 0 ∧ d2 f 0 < 0.0052182 := by
  sorry

theorem blind_neg1988_exists :
    ∃ f : ℝ → ℝ, IsSolution f ∧ Attached f ∧ SuperExpApproach f := by
  sorry

end Neg1988Blind
