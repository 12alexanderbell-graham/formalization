import Mathlib.Data.Real.Basic
/-! Blind literal reading of three tabulated Falkner–Skan wedge rows with decelerating outer stream, copied from `runs/2026-11-13T1640Z/fsatt_reader3/SecondReadingFSAttRowsTop.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, checked it with sympy and read the pressure-gradient parameters from a typeset crop of the table. Rows are counted from the top of the cropped segment of the table, which holds the rows with decelerating outer stream. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the first row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopFirstRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-13 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the second row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopSecondRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-14 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the fourth row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopFourthRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-16 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
