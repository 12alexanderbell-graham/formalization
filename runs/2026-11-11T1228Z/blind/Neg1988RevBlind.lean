import Mathlib

open Filter Set

namespace Neg1988RevBlind

/-- The wall-parameter beta = -0.1988. -/
noncomputable def β : ℝ := -0.1988

/-- First derivative on `[0, ∞)`. -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
/-- Second derivative on `[0, ∞)`. -/
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
/-- Third derivative on `[0, ∞)`. -/
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- Falkner–Skan ODE on the closed half-line, with `C³` regularity there
(no boundary conditions). -/
def FSOde (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 f (Ici 0) ∧
  ∀ η ∈ Ici (0 : ℝ), d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0

/-- Wall conditions `f(0) = 0`, `f'(0) = 0`. -/
def Wall (f : ℝ → ℝ) : Prop := f 0 = 0 ∧ d1 f 0 = 0

/-- Far-field condition `f' → 1`. -/
def Outer (f : ℝ → ℝ) : Prop := Tendsto (d1 f) atTop (nhds 1)

/-- Approach to the outer flow faster than any exponential rate. -/
def SuperExp (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η

/-- Full boundary-value problem solution. -/
def FSSol (f : ℝ → ℝ) : Prop := FSOde f ∧ Wall f ∧ Outer f

theorem blind_rev_window :
    ∃ f : ℝ → ℝ, FSSol f ∧ (∀ η ∈ Ici (0 : ℝ), |d1 f η| ≤ 1) ∧ SuperExp f ∧
      (-0.00515743 : ℝ) < d2 f 0 ∧ d2 f 0 < -0.00515741 := by
  sorry

theorem blind_rev_printed (f : ℝ → ℝ) (hf : FSOde f) (hw : Wall f)
    (h2 : d2 f 0 = -0.005158) :
    ∃ η : ℝ, 0 < η ∧ 1 < d1 f η := by
  sorry

theorem blind_rev_two :
    ∃ f g : ℝ → ℝ, FSSol f ∧ FSSol g ∧
      (∀ η ∈ Ici (0 : ℝ), |d1 f η| ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), |d1 g η| ≤ 1) ∧
      SuperExp f ∧ SuperExp g ∧ d2 f 0 ≠ d2 g 0 := by
  sorry

end Neg1988RevBlind
