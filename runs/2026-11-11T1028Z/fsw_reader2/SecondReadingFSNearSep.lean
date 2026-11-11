import Mathlib.Data.Real.Basic
/-! Blind literal reading of a tabulated Falkner–Skan wedge row with decelerating outer stream (reader: Claude blind reader 2; derivation and checks: hand derivation, sympy substitution into the boundary-layer momentum equation, pdftotext and rendered PNG of arXiv:1212.5057v1 page 16). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow at the tabulated decelerating row near separation: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsNearSepWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)
end Checked.Trust.SecondReading
