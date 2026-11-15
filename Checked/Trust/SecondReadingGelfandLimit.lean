import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic
/-! Blind literal reading for the limit of the radial Gelfand branch in the three-dimensional ball: the branch parameter of the regular solution tends to the parameter of the singular radial solution. Copied verbatim (code) from `runs/2026-11-15T1228Z/gelfand_limit_reader/SecondReadingGelfandLimit.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder; the reader derived the value from the explicit singular solution and checked it numerically. Nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Gelfand problem in the three-dimensional unit ball: the radial branch parameter λ(s) = s² e^{w(s)} of the regular solution w tends, as s tends to infinity, to the value of the parameter of the singular radial solution. -/
def gelfandBranchLimit (w : ℝ → ℝ) : Prop := Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 2)
end Checked.Trust.SecondReading
