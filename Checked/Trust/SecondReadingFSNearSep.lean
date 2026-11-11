import Mathlib.Data.Real.Basic
/-! Blind literal reading of a tabulated Falkner–Skan wedge row with decelerating outer stream, copied from `runs/2026-11-11T1028Z/fsw_reader2/SecondReadingFSNearSep.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables and read the pressure-gradient parameter from the typeset arXiv page. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the tabulated decelerating row near separation: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsNearSepWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
