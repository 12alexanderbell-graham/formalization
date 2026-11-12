import Mathlib.Data.Real.Basic
/-! Blind literal reading of two printed Falkner–Skan wall values (reader: second blind reader, source: R. Fazio, arXiv:1212.5057v1 (2012), page 16, β = -0.1988). -/
namespace Checked.Trust.SecondReading
/-- Fazio (arXiv:1212.5057, 2012): the printed missing initial condition d²f/dη²(0) of the normal-flow Falkner–Skan solution in the example of the extended algorithm. -/
noncomputable def fsAttPrintedWallValueFazio : ℝ := 0.005221
/-- Fazio (arXiv:1212.5057, 2012): the printed missing initial condition d²f/dη²(0) of the reverse-flow Falkner–Skan solution in the example of the extended algorithm. -/
noncomputable def fsRevPrintedWallValueFazio : ℝ := -0.005158
end Checked.Trust.SecondReading
