import Mathlib.Data.Real.Basic
/-! Blind literal reading of one tabulated Falkner–Skan wedge row with decelerating outer stream, copied from `runs/2026-11-12T1428Z/fsatt_reader2/SecondReadingFSAttRowTop.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, checked it with sympy and read the pressure-gradient parameter from a typeset crop of the table. Rows are counted from the top of the cropped segment of the table, which holds the rows with decelerating outer stream. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the third row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopThirdRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-15 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
