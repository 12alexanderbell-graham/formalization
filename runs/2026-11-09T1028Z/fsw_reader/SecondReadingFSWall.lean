import Mathlib.Data.Real.Basic
/-! Blind literal reading of the wall value in a Falkner–Skan problem (reader: Claude subagent; derivation and sources: the brief only, hand differentiation of the stream function, no external sources). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan problem: the wall value of q = f'', to which the wall shear stress is proportional. -/
def fsnWallValue (q : ℝ → ℝ) : ℝ := q 0
end Checked.Trust.SecondReading
