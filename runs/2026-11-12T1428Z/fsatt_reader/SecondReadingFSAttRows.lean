import Mathlib.Data.Real.Basic
/-! Blind literal reading of three tabulated Falkner–Skan wedge rows with decelerating outer stream (reader: Claude Sonnet 5.5 subagent; derivation and checks: hand derivation of f''' + f f'' + β (1 - f'^2) = 0 with β = 2m/(m+1), sympy substitution of ψ into the boundary-layer momentum equation, and the cropped image of Table 6 of arXiv:1006.3888v1). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the third-from-last row of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttThirdRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-17 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the second-from-last row of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttSecondRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-18 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the last row of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttLastRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-19 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
