import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan separation window (reader: independent sub-agent; method: (a) mpmath Taylor odefun shooting from f=p=q=0 with bisection on beta, 40 digits, giving beta* = -0.19883773504667744..-0.19883773504667758; (b) scipy DOP853 rtol 2.3e-14 shooting with event bisection, giving beta* = -0.1988377350466777; agree to about 15 digits). -/
namespace Checked.Trust.SecondReading
open Set
/-- Falkner–Skan separation: β lies strictly between the outward ten-decimal roundings of the separation value β*. -/
def fsSepWindow (β : ℝ) : Prop := β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000))
/-- Falkner–Skan problem: the open half-line of η beyond the wall. -/
def fsSepOpenHalfLine : Set ℝ := Ioi (0 : ℝ)
end Checked.Trust.SecondReading
