import Mathlib.Data.Real.Basic
/-! Blind literal reading of one tabulated Falkner–Skan wedge row with decelerating outer stream, reversed-flow table (reader: independent blind reader; derivation and checks: hand derivation of f''' + f f'' + β(1 - f'^2) = 0 with β = 2m/(m+1), sympy substitution into the boundary-layer momentum equation, Ganapol arXiv:1006.3888v1 Table 7 crop). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at one row of the reversed-flow table (the row this definition's placeholder names in the brief): the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowWantedRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-3 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
