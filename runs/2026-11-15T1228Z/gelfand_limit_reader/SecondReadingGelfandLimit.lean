import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
/-! Blind literal reading for the limit of the radial Gelfand branch in the three-dimensional ball. -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Gelfand problem in the three-dimensional unit ball: the radial branch parameter λ(s) = s² e^{w(s)} of the regular solution w tends, as s tends to infinity, to the value of the parameter of the singular radial solution. -/
def gelfandBranchLimit (w : ℝ → ℝ) : Prop := Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 2)
end Checked.Trust.SecondReading
