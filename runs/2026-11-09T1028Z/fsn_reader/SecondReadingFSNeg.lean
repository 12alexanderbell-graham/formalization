import Mathlib.Data.Real.Basic
/-! Blind literal reading of a Falkner–Skan wedge problem with decelerating outer stream (reader: Claude subagent (fsn_reader); derivation, checks and sources: own derivation with sympy substitution of psi into the boundary-layer equation, edge linearisation checked in sympy, scipy shooting; no web or repository sources). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = −1/21: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsnWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-1 / 10) * (1 - p η ^ 2)
/-- Falkner–Skan problem: at height η, q = f'' is at least M times the velocity defect, the edge value of p = f' minus p η. -/
def fsnDefectBelow (M : ℝ) (p q : ℝ → ℝ) (η : ℝ) : Prop := M * (1 - p η) ≤ q η
end Checked.Trust.SecondReading
