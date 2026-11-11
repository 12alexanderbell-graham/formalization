import Mathlib.Data.Real.Basic
/-! Blind literal reading of the printed Falkner–Skan limiting parameter value (reader: independent blind reader, sources: Fazio arXiv:1212.5057v? PDF page 28, Figure 4 caption; arXiv:2011.07725v? PDF page 22, Figure 7 caption). Both captions print β = −0.1988376; the two papers agree. -/
namespace Checked.Trust.SecondReading
/-- Fazio (arXiv:1212.5057, 2012; arXiv:2011.07725, 2020): the value of β printed in the figure caption of the solution with zero wall shear d²f/dη²(0) = 0, all printed digits, with its sign. -/
noncomputable def fsSepPrintedFazio : ℝ := -(1988376 / 10000000)
end Checked.Trust.SecondReading
