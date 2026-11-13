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
import Checked.FSAtt.RThirteenLo
import Checked.FSAtt.RThirteenHi
import Checked.FSAtt.RThirteenCore
import Checked.FSAtt.RFourteenLo
import Checked.FSAtt.RFourteenHi
import Checked.FSAtt.RFourteenCore
import Checked.FSAtt.RFifteenLo
import Checked.FSAtt.RFifteenHi
import Checked.FSAtt.RFifteenCore
import Checked.FSAtt.RSixteenLo
import Checked.FSAtt.RSixteenHi
import Checked.FSAtt.RSixteenCore

/-! Falkner–Skan with adverse pressure gradient at the first four rows of the decelerating segment of an attached wall-shear table read blind: the wall shear of every solution with positive second derivative that approaches the edge value faster than every exponential, and the existence of such a solution, one pair per row. Module `NegWallShearRowsTop`, promoted from `Work/FalknerSkan/AttachedRowsTop.lean` (theorems `fs_att_thirteen_window`, `fs_att_fourteen_window`, `fs_att_sixteen_window`) and `Work/FalknerSkan/AttachedRows.lean` (theorem `fs_att_fifteen_window`), with their existence companions there. -/

namespace Checked.FalknerSkan.NegWallShearRowsTop

open Set Filter Topology

/-- Falkner–Skan with β = −13/100: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.2614227559 < q(0) < 0.2614227560. -/
theorem fs_neg_wall_shear_13_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.2614227559 < q 0 ∧ q 0 < 0.2614227560 :=
  Checked.FSAtt.RThirteenCore.window_core Checked.FSAtt.RThirteenLo.chain Checked.FSAtt.RThirteenHi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −13/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_neg_wall_shear_13_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-13 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Checked.FSAtt.RThirteenCore.exists_core Checked.FSAtt.RThirteenLo.chain Checked.FSAtt.RThirteenHi.chain

/-- Falkner–Skan with β = −14/100: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.2397359553 < q(0) < 0.2397359554. -/
theorem fs_neg_wall_shear_14_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.2397359553 < q 0 ∧ q 0 < 0.2397359554 :=
  Checked.FSAtt.RFourteenCore.window_core Checked.FSAtt.RFourteenLo.chain Checked.FSAtt.RFourteenHi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −14/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_neg_wall_shear_14_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Checked.FSAtt.RFourteenCore.exists_core Checked.FSAtt.RFourteenLo.chain Checked.FSAtt.RFourteenHi.chain

/-- Falkner–Skan with β = −15/100: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.2163614056 < q(0) < 0.2163614057. -/
theorem fs_neg_wall_shear_15_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-15 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.2163614056 < q 0 ∧ q 0 < 0.2163614057 :=
  Checked.FSAtt.RFifteenCore.window_core Checked.FSAtt.RFifteenLo.chain Checked.FSAtt.RFifteenHi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −15/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_neg_wall_shear_15_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-15 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Checked.FSAtt.RFifteenCore.exists_core Checked.FSAtt.RFifteenLo.chain Checked.FSAtt.RFifteenHi.chain

/-- Falkner–Skan with β = −16/100: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞)
with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`,
then 0.1907798552 < q(0) < 0.1907798553. -/
theorem fs_neg_wall_shear_16_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-16 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.1907798552 < q 0 ∧ q 0 < 0.1907798553 :=
  Checked.FSAtt.RSixteenCore.window_core Checked.FSAtt.RSixteenLo.chain Checked.FSAtt.RSixteenHi.chain
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −16/100: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0 on
[0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`. -/
theorem fs_neg_wall_shear_16_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-16 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :=
  Checked.FSAtt.RSixteenCore.exists_core Checked.FSAtt.RSixteenLo.chain Checked.FSAtt.RSixteenHi.chain

end Checked.FalknerSkan.NegWallShearRowsTop
