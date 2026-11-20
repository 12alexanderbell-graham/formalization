import Mathlib.Data.Real.Basic
/-! Blind literal reading for the turning values of the radial Gelfand branch: the positions of the second, third and fourth turning points of the branch parameter in the sequence of turning points. Copied verbatim (code) from `runs/2026-11-20T1028Z/turn_reader/SecondReadingGelfandTurns.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the claim's own description of the numbering; nothing external consulted. -/
namespace Checked.Trust.SecondReading
/-- Radial Gelfand problem (isothermal sphere): the radius, in the sequence ζ of turning points of the branch parameter, of the second turning point (the first minimum). -/
def gelfandSecondTurn (ζ : ℕ → ℝ) : ℝ := ζ 1
/-- Radial Gelfand problem (isothermal sphere): the radius, in the sequence ζ of turning points of the branch parameter, of the third turning point (the second maximum). -/
def gelfandThirdTurn (ζ : ℕ → ℝ) : ℝ := ζ 2
/-- Radial Gelfand problem (isothermal sphere): the radius, in the sequence ζ of turning points of the branch parameter, of the fourth turning point (the second minimum). -/
def gelfandFourthTurn (ζ : ℕ → ℝ) : ℝ := ζ 3
end Checked.Trust.SecondReading
