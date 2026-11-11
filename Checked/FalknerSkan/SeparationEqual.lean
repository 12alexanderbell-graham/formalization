import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.IntermediateValue
import Checked.FSSep.UPair

/-! Falkner–Skan separation: two pressure-gradient parameters with zero-wall-shear solutions approaching the edge value faster than every exponential are equal. Module `SeparationEqual`, promoted from `Work/FalknerSkan/SeparationUnique.lean`. -/

namespace Checked.FalknerSkan.SeparationEqual

open Set Filter Topology

/-- Falkner–Skan separation: for every solution (f₁, p₁, q₁) of f''' + f f'' + β₁(1 − f'²) = 0 and every
solution (f₂, p₂, q₂) of f''' + f f'' + β₂(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, wall
shear q(0) = 0, p → 1, q > 0 on (0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₁ η) ≤ q₁ η` and
`∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`: β₁ = β₂. -/
theorem fs_separation_equal {β₁ β₂ : ℝ} {f₁ p₁ q₁ f₂ p₂ q₂ : ℝ → ℝ}
    (hf₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₁ (p₁ η) (Ici 0) η)
    (hp₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₁ (q₁ η) (Ici 0) η)
    (hq₁ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₁ (-(f₁ η * q₁ η) - β₁ * (1 - p₁ η ^ 2)) (Ici 0) η)
    (hf₁0 : f₁ 0 = 0) (hp₁0 : p₁ 0 = 0) (hq₁0 : q₁ 0 = 0) (hl₁ : Tendsto p₁ atTop (𝓝 1))
    (hpos₁ : ∀ η ∈ Ioi (0 : ℝ), 0 < q₁ η) (hdec₁ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₁ η) ≤ q₁ η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β₂ * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hq₂0 : q₂ 0 = 0) (hl₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ioi (0 : ℝ), 0 < q₂ η) (hdec₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    β₁ = β₂ := by
  have S₁ : Checked.FSSep.UCompare.SolB β₁ f₁ p₁ q₁ := ⟨hf₁, hp₁, hq₁, hf₁0, hp₁0, hq₁0, hl₁, hpos₁⟩
  have S₂ : Checked.FSSep.UCompare.SolB β₂ f₂ p₂ q₂ := ⟨hf₂, hp₂, hq₂, hf₂0, hp₂0, hq₂0, hl₂, hpos₂⟩
  rcases lt_trichotomy β₁ β₂ with h | h | h
  · exact (Checked.FSSep.UPair.sep_core h S₁ S₂ hdec₂).elim
  · exact h
  · exact (Checked.FSSep.UPair.sep_core h S₂ S₁ hdec₁).elim

end Checked.FalknerSkan.SeparationEqual

