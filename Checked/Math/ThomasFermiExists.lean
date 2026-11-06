import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Checked.Math.TFExAssemble

/-! Thomas–Fermi, `ThomasFermiExists`: existence of a solution meeting every hypothesis of the Thomas–Fermi slope headline. Promoted from `Work/Math/ThomasFermiExists.lean`. -/

namespace Checked.Math.ThomasFermiExists
open Set Filter Topology

/-- There is a solution y of the Thomas–Fermi equation y'' = y^{3/2}/√x on (0, ∞) with y' = φ on
[0, ∞), φ continuous at 0 from the right, y(0) = 1, y > 0 on [0, ∞) and y(x) → 0 as x → ∞. -/
theorem tf_exists : ∃ y φ : ℝ → ℝ,
    (∀ x, 0 ≤ x → HasDerivWithinAt y (φ x) (Ici 0) x) ∧
    (∀ x, 0 < x → HasDerivAt φ (y x ^ ((3 : ℝ) / 2) / Real.sqrt x) x) ∧
    ContinuousWithinAt φ (Ici 0) 0 ∧ y 0 = 1 ∧ (∀ x, 0 ≤ x → 0 < y x) ∧
    Tendsto y atTop (𝓝 0) := by
  obtain ⟨U, P, hU, hP, h0, hpos, hlim⟩ := Checked.Math.TFExAssemble.main
  exact Checked.Math.TFExConvert.convert U P hU hP h0 hpos hlim

end Checked.Math.ThomasFermiExists
