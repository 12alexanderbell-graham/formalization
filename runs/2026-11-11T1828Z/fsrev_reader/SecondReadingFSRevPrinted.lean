import Mathlib.Data.Real.Basic
/-! Blind literal reading of the printed reverse-flow Falkner–Skan wall value (reader: fsrev_reader, source: R. Fazio, arXiv:1212.5057v1, printed page 16, β = −0.1988 with normal-flow value 0.005221 printed alongside). -/
namespace Checked.Trust.SecondReading
/-- Fazio (arXiv:1212.5057, 2012): the printed missing initial condition d²f/dη²(0) of the reverse-flow Falkner–Skan solution in the example of the extended algorithm, as the wall condition on q = f''. -/
def fsRevPrintedWallFazio (q : ℝ → ℝ) : Prop := q 0 = -0.005158
end Checked.Trust.SecondReading
