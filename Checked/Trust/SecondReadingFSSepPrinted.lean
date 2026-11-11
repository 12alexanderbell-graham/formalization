import Mathlib.Data.Real.Basic
/-! Blind literal reading of the value of the Falkner–Skan parameter printed by Fazio (his 2012 and 2020 arXiv papers, version 1 of each: the Figure 4 caption of the first and the Figure 7 caption of the second print the same value; typeset pages seen) for the solution with zero wall shear (run 2026-11-11T0828Z). Copied verbatim (code) from `runs/2026-11-11T0828Z/sep_printed_reader/SecondReadingFSSepPrinted.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder; the reader left the arXiv versions unrecorded, both papers exist only in version 1. -/
namespace Checked.Trust.SecondReading
/-- Fazio (arXiv:1212.5057, 2012; arXiv:2011.07725, 2020): the value of β printed in the figure caption of the solution with zero wall shear d²f/dη²(0) = 0, all printed digits, with its sign. -/
noncomputable def fsSepPrintedFazio : ℝ := -(1988376 / 10000000)
end Checked.Trust.SecondReading
