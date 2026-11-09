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
import Checked.FalknerSkan.NegTenth

/-! Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth: two solutions with different wall shear, neither in the fast-approach class. Module `NegOutside`, promoted from `Work/FalknerSkan/NegOutside.lean`. -/

namespace Checked.FalknerSkan.NegOutside

open Set Filter Topology

/-- Falkner–Skan with β = −1/10: there are solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, q > 0 and 0 ≤ p ≤ 1 on
[0, ∞), with q(0) ≠ q₂(0), such that it is not the case that, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, and it is not the case that,
for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p₂ η) ≤ q₂ η`. -/
theorem fs_neg_tenth_outside_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1 / 10) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q₂ η ∧ 0 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      ¬ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      ¬ (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  obtain ⟨f, p, q, f₂, p₂, q₂, hf, hp, hq, hf₂, hp₂, hq₂, h0, h1, h2, h3, hl, hl₂, hb, hb₂,
    hs, hs₂, hne⟩ := Checked.FalknerSkan.NegTenth.fs_neg_tenth_not_unique
  refine ⟨f, p, q, f₂, p₂, q₂, hf, hp, hq, hf₂, hp₂, hq₂, h0, h1, h2, h3, hl, hl₂, hb, hb₂,
    ?_, ?_, hne⟩
  · intro h
    obtain ⟨η, h1, h2⟩ := ((h 3).and hs).exists
    linarith
  · intro h
    obtain ⟨η, h1, h2⟩ := ((h 3).and hs₂).exists
    linarith

end Checked.FalknerSkan.NegOutside
