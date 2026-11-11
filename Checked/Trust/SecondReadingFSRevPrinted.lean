import Mathlib.Data.Real.Basic
/-! Blind literal reading of the reverse-flow Falkner–Skan wall value printed by Fazio (his 2012 arXiv paper, version 1; typeset page seen), copied from `runs/2026-11-11T1828Z/fsrev_reader/SecondReadingFSRevPrinted.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief committed alone before it in that folder. -/
namespace Checked.Trust.SecondReading
/-- Fazio (arXiv:1212.5057, 2012): the printed missing initial condition d²f/dη²(0) of the reverse-flow Falkner–Skan solution in the example of the extended algorithm, as the wall condition on q = f''. -/
def fsRevPrintedWallFazio (q : ℝ → ℝ) : Prop := q 0 = -0.005158
end Checked.Trust.SecondReading
