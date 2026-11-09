import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan equation with a general parameter (reader: Claude subagent, blind reader; derivation, check and sources: own derivation by chain rule from the stream function, verified symbolically with sympy for general m, plus the m = 0 Blasius and m = 1 Hiemenz special cases; no external sources consulted). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with outer stream a·x^m and parameter β = 2*m/(m+1): the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsBetaRhs (β : ℝ) (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - β * (1 - p η ^ 2)
end Checked.Trust.SecondReading
