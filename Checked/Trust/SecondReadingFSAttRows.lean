import Mathlib.Data.Real.Basic
/-! Blind literal reading of three tabulated Falkner–Skan wedge rows with decelerating outer stream, copied from `runs/2026-11-12T1428Z/fsatt_reader/SecondReadingFSAttRows.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, checked it with sympy and read the pressure-gradient parameters from a typeset crop of the table. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the third-from-last row of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttThirdRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-17 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the second-from-last row of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttSecondRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-18 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the last row of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttLastRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-19 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
