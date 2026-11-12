import Mathlib.Data.Real.Basic
/-! Blind literal reading of one tabulated Falkner–Skan wedge row with decelerating outer stream (reader: Claude subagent, blind reader 2; derivation and checks: hand derivation plus sympy substitution of psi into the boundary-layer momentum equation, image crop of Table 6). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the third row from the top of the table: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsAttTopThirdRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-15 / 100) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
