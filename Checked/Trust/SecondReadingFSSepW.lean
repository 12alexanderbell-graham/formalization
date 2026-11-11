import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan separation window and of the open half-line beyond the wall (reader: an independent Sonnet sub-agent with two numerical routes; brief and reading in the `sep_reader3` folder of the run that promoted the separation theorems). -/
namespace Checked.Trust.SecondReading
open Set
/-- Falkner–Skan separation: β lies strictly between the outward ten-decimal roundings of the separation value β*. -/
def fsSepWindow (β : ℝ) : Prop := β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000))
/-- Falkner–Skan problem: the open half-line of η beyond the wall. -/
def fsSepOpenHalfLine : Set ℝ := Ioi (0 : ℝ)
end Checked.Trust.SecondReading
