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
import Checked.FSNeg.NAssemble
import Checked.FSNeg.NSlowHalf
import Checked.FSNeg.NSlow34
import Checked.FSNeg.NOver11

/-! Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth: existence in the fast-approach class, and two solutions with different wall shear outside it. Module `NegTenth`, promoted from `Work/FalknerSkan/NegTenth.lean`. -/

namespace Checked.FalknerSkan.NegTenth

open Set Filter Topology

/-- Falkner–Skan with β = −1/10: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_neg_tenth_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  exact Checked.FSNeg.NAssemble.core_exists ⟨9 / 8, by norm_num, fun Y hY h0 => Checked.FSNeg.NSlow34.chainC hY h0⟩
    ⟨5 / 4, by norm_num, fun Y hY h0 => Checked.FSNeg.NOver11.chainC hY h0⟩

/-- Falkner–Skan with β = −1/10: there are two solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, q > 0 and
0 ≤ p ≤ 1 on [0, ∞), and eventually q < 3 (1 − p), whose values q(0) and q₂(0) differ. -/
theorem fs_neg_tenth_not_unique :
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
      (∀ᶠ η in atTop, q η < 3 * (1 - p η)) ∧ (∀ᶠ η in atTop, q₂ η < 3 * (1 - p₂ η)) ∧
      q 0 ≠ q₂ 0 := by
  exact Checked.FSNeg.NAssemble.core_not_unique
    ⟨5 / 4, by norm_num, fun Y hY h0 => Checked.FSNeg.NSlowHalf.chainC hY h0⟩
    ⟨9 / 8, by norm_num, fun Y hY h0 => Checked.FSNeg.NSlow34.chainC hY h0⟩

end Checked.FalknerSkan.NegTenth
