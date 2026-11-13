import Mathlib.Data.Real.Basic
/-! Blind literal reading of three tabulated Falkner–Skan wedge rows with decelerating outer stream (reader: Claude, independent; derivation and checks: sympy substitution of ψ into the boundary-layer momentum equation, giving f''' + f f'' + β (1 - f'^2) = 0 with β = 2m/(m+1); pdftotext confirmation of Table 6, page 21). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the first row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopFirstRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-13 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the second row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopSecondRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-14 / 100) * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow at the fourth row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopFourthRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-16 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
