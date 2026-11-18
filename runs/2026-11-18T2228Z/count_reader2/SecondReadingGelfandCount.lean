import Mathlib.Analysis.SpecialFunctions.Exp
/-! Blind literal reading for the number of radial solutions of the Gelfand problem in the ball (run 2026-11-18T2228Z). -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Gelfand problem in the ball: the first maximum value of the branch parameter, for the sequence l of turning values. -/
def gcFirstMax (l : ℕ → ℝ) : ℝ := l 0
/-- Gelfand problem in the ball: the first minimum value of the branch parameter, for the sequence l of turning values. -/
def gcFirstMin (l : ℕ → ℝ) : ℝ := l 1
/-- Gelfand problem in the ball: the second maximum value of the branch parameter, for the sequence l of turning values. -/
def gcSecondMax (l : ℕ → ℝ) : ℝ := l 2
/-- Gelfand problem in the ball: the index of the (k+1)-th maximum in the sequence of turning values. -/
def gcMaxIndex (k : ℕ) : ℕ := 2 * k
/-- Gelfand problem in the ball: the index of the (k+1)-th minimum in the sequence of turning values. -/
def gcMinIndex (k : ℕ) : ℕ := 2 * k + 1
/-- Gelfand problem in the ball: the index of the (k+2)-th maximum in the sequence of turning values. -/
def gcNextMaxIndex (k : ℕ) : ℕ := 2 * k + 2
/-- Gelfand problem in the ball: the index of the (k+2)-th minimum in the sequence of turning values. -/
def gcNextMinIndex (k : ℕ) : ℕ := 2 * k + 3
/-- Gelfand problem in the ball: the turning values tend to the parameter of the singular solution. -/
def gcLimit (l : ℕ → ℝ) : Prop := Tendsto l atTop (𝓝 2)
/-- Gelfand problem in the ball: a minimum value a lies below and a maximum value b above the parameter of the singular solution. -/
def gcSeparate (a b : ℝ) : Prop := a < 2 ∧ 2 < b
/-- Gelfand problem in the ball: the equation at the parameter of the singular solution, for the value L of the Laplacian and the value v of the function at a point. -/
def gcSingularEq (L v : ℝ) : Prop := L + 2 * Real.exp v = 0
/-- Gelfand problem in the ball: the number of radial solutions for a parameter strictly between the value at the (k+2)-th maximum and the value at the (k+1)-th maximum. -/
def gcCountFallBand (k : ℕ) : ℕ := 2 * k + 2
/-- Gelfand problem in the ball: the number of radial solutions for a parameter equal to the value at the (k+2)-th maximum. -/
def gcCountAtMax (k : ℕ) : ℕ := 2 * k + 3
/-- Gelfand problem in the ball: the number of radial solutions for a parameter equal to the value at the (k+1)-th minimum. -/
def gcCountAtMin (k : ℕ) : ℕ := 2 * k + 2
/-- Gelfand problem in the ball: the number of radial solutions for a parameter strictly between the value at the (k+1)-th minimum and the value at the (k+2)-th minimum. -/
def gcCountRiseBand (k : ℕ) : ℕ := 2 * k + 3
end Checked.Trust.SecondReading
