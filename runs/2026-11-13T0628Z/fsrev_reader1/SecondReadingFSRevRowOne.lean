import Mathlib.Data.Real.Basic
/-! Blind literal reading of one tabulated Falkner–Skan wedge row with decelerating outer stream, reversed-flow table (reader: blind reader 1; derivation and checks: hand derivation with sympy substitution of psi into the boundary-layer momentum equation, Ganapol Table 7 crop image). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at one row of the reversed-flow table (the row this definition's placeholder names in the brief): the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsRevRowOneRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-1 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
