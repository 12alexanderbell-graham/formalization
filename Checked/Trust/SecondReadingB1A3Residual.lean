import Mathlib.Analysis.SpecialFunctions.Log.Base
/-! Blind literal reading of the residual condition of the three-source cubic fit. Copied verbatim (code) from `runs/2026-11-21T1628Z/lit_reader4/SecondReadingB1A3Residual.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the claim in words in the brief; nothing external consulted. -/
namespace Checked.Trust.SecondReading
/-- Three-source cubic fit: the distance modulus of the ratio `d` is within the window of the common offset `c`. -/
def b1a3Residual (d c : ℝ) : Prop := |5 * Real.logb 10 d - c| ≤ 1 / 20
end Checked.Trust.SecondReading
