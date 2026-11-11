import Mathlib.Data.Real.Basic
/-! Blind literal reading of the Falkner–Skan separation window (reader: sep_reader3; method: (a) mpmath Taylor integrator at 40 digits, bisection on beta by first p>1 vs staying below, cutoff eta=12 and 14: -0.19883773504667754689; (b) scipy DOP853 rtol 1e-13 bisection, cutoff 12 and 16: -0.198837735046679; agree to 14 digits). -/
namespace Checked.Trust.SecondReading
open Set
/-- Falkner–Skan separation: β lies strictly between the outward ten-decimal roundings of the separation value β*. -/
def fsSepWindow (β : ℝ) : Prop := β ∈ Ioo (-(1988377351 / 10000000000 : ℝ)) (-(1988377350 / 10000000000))
/-- Falkner–Skan problem: the open half-line of η beyond the wall. -/
def fsSepOpenHalfLine : Set ℝ := Ioi (0 : ℝ)
end Checked.Trust.SecondReading
