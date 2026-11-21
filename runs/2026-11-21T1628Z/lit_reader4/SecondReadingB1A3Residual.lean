import Mathlib.Analysis.SpecialFunctions.Log.Base
/-! Blind literal reading of the residual condition of the three-source cubic fit (run 2026-11-21T1628Z). -/
namespace Checked.Trust.SecondReading
/-- Three-source cubic fit: the distance modulus of the ratio `d` is within the window of the common offset `c`. -/
def b1a3Residual (d c : ℝ) : Prop := |5 * Real.logb 10 d - c| ≤ 1 / 20
end Checked.Trust.SecondReading
