import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan wedge problem with the exponent of the outer stream one nineteenth, copied from `runs/2026-11-08T2028Z/fst_reader/SecondReadingFSTenth.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Claude subagent from the brief next to it alone; it derived the equation from the wedge-flow similarity variables, found the pressure-gradient coefficient as an exact fraction of the wedge exponent, and computed the wall value by its own high-precision shooting computation; no outside sources. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = 1/19: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fstWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - 1 / 10 * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow with m = 1/19: the wall value of q = f'' lies strictly between σ − 10⁻¹⁰ and σ + 10⁻¹⁰, each rounded to ten decimals. -/
def fstWedgeShear (q : ℝ → ℝ) : Prop := 0.5870352191 < q 0 ∧ q 0 < 0.5870352193
end Checked.Trust.SecondReading
