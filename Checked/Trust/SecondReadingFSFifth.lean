import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan wedge problem with the exponent of the outer stream one ninth, copied from `runs/2026-11-08T2028Z/fs_reader/SecondReadingFSFifth.lean` (code verbatim; module doc rewritten without numbers). Reader: an independent Sonnet subagent from brief 0e29796 alone; it derived the equation from the wedge-flow similarity variables, found the pressure-gradient coefficient as an exact fraction of the wedge exponent, and computed the wall value by high-precision shooting at two precisions and a second integrator; no outside sources. -/
namespace Checked.Trust.SecondReading
/-- Falkner–Skan wedge flow with m = 1/9: the right-hand side of q' (where p = f' and q = f'') at η. -/
noncomputable def fsfWedgeRhs (f p q : ℝ → ℝ) (η : ℝ) : ℝ := -(f η * q η) - 1 / 5 * (1 - p η ^ 2)
/-- Falkner–Skan wedge flow with m = 1/9: the wall value of q = f'' lies strictly between σ − 10⁻¹⁰ and σ + 10⁻¹⁰, each rounded to ten decimals. -/
def fsfWedgeShear (q : ℝ → ℝ) : Prop := 0.6867081809 < q 0 ∧ q 0 < 0.6867081811
end Checked.Trust.SecondReading
