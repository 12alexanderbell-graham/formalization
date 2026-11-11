import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan separation window (reader: sep_reader2; method: (a) mpmath odefun shooting from f=p=q=0 at 40 digits with bisection on overshoot of p above 1, giving beta* = -0.19883773504667755; (b) scipy DOP853 shooting with p(L)=1 at L = 6, 8, 10, 12, giving beta* = -0.198837735046678 at L = 12; agreement to about 4e-16). -/
namespace Checked.Trust.SecondReading
open Set
/-- Falkner–Skan separation: β lies strictly between the outward ten-decimal roundings of the separation value β*. -/
def fsSepWindow (β : ℝ) : Prop := β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000))
/-- Falkner–Skan problem: the open half-line of η beyond the wall. -/
def fsSepOpenHalfLine : Set ℝ := Ioi (0 : ℝ)
end Checked.Trust.SecondReading
