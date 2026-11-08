import Mathlib.Data.Real.Basic
/-! Blind literal reading of a Falkner–Skan wedge problem (reader: Claude subagent; derivation, computation and sources: own derivation of f''' + f f'' + (2m/(m+1))(1 - f'^2) = 0, own mpmath shooting at 35 and 40 digits plus scipy DOP853 check; no external sources). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = 1/9: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsfWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - 1 / 5 * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow with m = 1/9: the wall value of q = f'' lies strictly between σ − 10⁻¹⁰ and σ + 10⁻¹⁰, each rounded to ten decimals. -/
def fsfWedgeShear (q : ℝ → ℝ) : Prop := 0.6867081809 < q 0 ∧ q 0 < 0.6867081811
end Checked.Trust.SecondReading
