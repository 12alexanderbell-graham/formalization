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
import Checked.FSNeg.NWindow
import Checked.FSNeg.NWinLo
import Checked.FSNeg.NWinHi

/-! Falkner–Skan with the adverse pressure-gradient coefficient of minus one tenth: the wall shear of every solution with positive second derivative that approaches the edge value faster than every exponential, and an upper bound for every solution with positive second derivative. Module `NegWindow`, promoted from `Work/FalknerSkan/NegWindow.lean`. -/

namespace Checked.FalknerSkan.NegWindow

open Set Filter Topology

/-- Falkner–Skan with β = −1/10: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, `∀ᶠ (η : ℝ) in Filter.atTop, M * (1 - p η) ≤ q η`, then
0.3192697598 < q(0) < 0.3192697599. -/
theorem fs_neg_tenth_window (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.3192697598 < q 0 ∧ q 0 < 0.3192697599 :=
  Checked.FSNeg.NWindow.ten_window
    ⟨3, by norm_num, fun _ hY h0 => Checked.FSNeg.NWinLo.chainC hY h0⟩
    ⟨11 / 4, by norm_num, fun _ hY h0 => Checked.FSNeg.NWinHi.chainC hY h0⟩
    f p q hf hp hq hf0 hp0 hlim hpos hdec

/-- Falkner–Skan with β = −1/10: if (f, p, q) is a solution of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1 and q > 0 on [0, ∞), then q(0) < 0.3192697599. -/
theorem fs_neg_tenth_monotone_lt (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η) :
    q 0 < 0.3192697599 :=
  Checked.FSNeg.NWindow.ten_monotone_lt
    ⟨3, by norm_num, fun _ hY h0 => Checked.FSNeg.NWinLo.chainC hY h0⟩
    ⟨11 / 4, by norm_num, fun _ hY h0 => Checked.FSNeg.NWinHi.chainC hY h0⟩
    f p q hf hp hq hf0 hp0 hlim hpos

end Checked.FalknerSkan.NegWindow
