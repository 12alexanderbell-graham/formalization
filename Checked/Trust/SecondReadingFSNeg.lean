import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan wedge problem with a decelerating outer stream, copied from `runs/2026-11-09T1028Z/fsn_reader/SecondReadingFSNeg.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables with a symbolic check of the momentum residual, found the pressure-gradient coefficient as an exact fraction of the wedge exponent, and derived the two kinds of approach to the edge value by linearisation, checked by its own shooting computation; no outside sources. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = −1/21: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsnWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - (-1 / 10) * (1 - p η ^ 2)
/-- Falkner–Skan problem: at height η, q = f'' is at least M times the velocity defect, the edge value of p = f' minus p η. -/
def fsnDefectBelow (M : ℝ) (p q : ℝ → ℝ) (η : ℝ) : Prop := M * (1 - p η) ≤ q η
end Checked.Trust.SecondReading
