import Mathlib.Data.Real.Basic
/-! Blind literal reading of one tabulated Falkner–Skan wedge row with decelerating outer stream, reversed-flow table, copied from `runs/2026-11-13T0228Z/fsrev_reader/SecondReadingFSRevTable.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, checked it with sympy and read the pressure-gradient parameter from a typeset crop of the table. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at one row of the reversed-flow table (the row this definition's placeholder names in the brief): the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowWantedRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-3 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
