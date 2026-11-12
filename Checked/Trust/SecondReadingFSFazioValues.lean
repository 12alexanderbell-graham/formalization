import Mathlib.Data.Real.Basic
/-! Blind literal reading of the two Falkner–Skan wall values printed by Fazio (his 2012 arXiv paper, version 1, the example sentence of the extended algorithm; typeset page crop seen), copied from `runs/2026-11-12T1028Z/fsval_reader/SecondReadingFSFazioValues.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief committed alone before it in that folder. -/
namespace Checked.Trust.SecondReading
/-- Fazio (arXiv:1212.5057, 2012): the printed missing initial condition d²f/dη²(0) of the normal-flow Falkner–Skan solution in the example of the extended algorithm. -/
noncomputable def fsAttPrintedWallValueFazio : ℝ := 0.005221
/-- Fazio (arXiv:1212.5057, 2012): the printed missing initial condition d²f/dη²(0) of the reverse-flow Falkner–Skan solution in the example of the extended algorithm. -/
noncomputable def fsRevPrintedWallValueFazio : ℝ := -0.005158
end Checked.Trust.SecondReading
