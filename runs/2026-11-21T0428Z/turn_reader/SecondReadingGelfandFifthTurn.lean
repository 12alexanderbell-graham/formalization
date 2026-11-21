import Mathlib.Data.Real.Basic
/-! Blind literal reading for the fifth turning value of the radial Gelfand branch (run 2026-11-21T0428Z). -/
namespace Checked.Trust.SecondReading
/-- Radial Gelfand problem (isothermal sphere): the radius, in the sequence ζ of turning points of the branch parameter, of the fifth turning point (the third maximum). -/
def gelfandFifthTurn (ζ : ℕ → ℝ) : ℝ := ζ 4
end Checked.Trust.SecondReading
