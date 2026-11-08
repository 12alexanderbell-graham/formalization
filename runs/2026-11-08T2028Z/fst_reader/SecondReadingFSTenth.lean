import Mathlib.Data.Real.Basic
/-! Blind literal reading of a Falkner–Skan wedge problem (reader: Claude subagent; derivation, computation and sources: own derivation of f''' + f f'' + β(1 − f'^2) = 0 with β = 2m/(m+1) = 1/10, and own mpmath shooting computation, no external sources). -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = 1/19: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fstWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - 1 / 10 * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow with m = 1/19: the wall value of q = f'' lies strictly between σ − 10⁻¹⁰ and σ + 10⁻¹⁰, each rounded to ten decimals. -/
def fstWedgeShear (q : ℝ → ℝ) : Prop := 0.5870352191 < q 0 ∧ q 0 < 0.5870352193
end Checked.Trust.SecondReading
