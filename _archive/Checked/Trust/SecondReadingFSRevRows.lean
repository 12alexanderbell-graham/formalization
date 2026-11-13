import Mathlib.Data.Real.Basic
/-! Blind literal reading of twelve tabulated Falkner–Skan wedge rows with decelerating outer stream, reversed-flow table, copied from `runs/2026-11-13T0028Z/fsrev_reader2/SecondReadingFSRevTable.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, checked it with sympy and read the pressure-gradient parameters from a typeset crop of the table. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the fourth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFourRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-4 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the fifth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFiveRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-5 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the sixth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowSixRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-6 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the seventh row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowSevenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-7 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the eighth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowEightRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-8 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the ninth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowNineRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-9 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the eleventh row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowElevenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-11 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the twelfth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowTwelveRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-12 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the thirteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowThirteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-13 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the fourteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFourteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-14 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the fifteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowFifteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-15 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the sixteenth row of the reversed-flow table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowSixteenRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-16 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
