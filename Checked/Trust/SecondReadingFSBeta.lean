import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan equation with a general pressure-gradient parameter, copied from `runs/2026-11-09T0428Z/fsb_reader/SecondReadingFSBeta.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables for a general wedge exponent, checked that the boundary-layer momentum residual vanishes identically with sympy and checked the flat-plate and plane stagnation-point cases; no outside sources. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with outer stream a·x^m and parameter β = 2*m/(m+1): the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsBetaRhs (β : ℝ) (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - β * (1 - p η ^ 2)
end Checked.Trust.SecondReading
