import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
/-! Blind literal reading for the multiplicity of radial solutions of the Gelfand problem in the unit ball (reader: Claude (many_reader); derivation, computation and sources: own derivation of the singular solution, own mpmath/Taylor integration of the Emden-Fowler-type ODE at 30 and 45 digits plus a scipy DOP853 cross-check; no web sources). -/
namespace Checked.Trust.SecondReading
/-- Gelfand problem in the ball, multiplicity: the equation at a point for the parameter value of the singular radial solution, with Lu the value of the Laplacian of the solution and v the value of the solution at that point. -/
def gelfandManyEqSingular (Lu v : ℝ) : Prop := Lu + 2 * Real.exp v = 0
/-- Gelfand problem in the ball, multiplicity: the parameter λ is within ε of the parameter value of the singular radial solution. -/
def gelfandManyNearSingular (lam ε : ℝ) : Prop := |lam - 2| < ε
/-- Gelfand problem in the ball, multiplicity: if λ is at least the parameter value of the singular radial solution then λ is below the reader's nine-decimal lower rounding of the critical parameter. -/
def gelfandManyTwoRange (lam : ℝ) : Prop := 2 ≤ lam → lam < 3.321992118
/-- Gelfand problem in the ball, multiplicity: the values at the centre of the ball of a sequence of functions on the space. -/
def gelfandManyCentreSeq (u : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ) : ℕ → ℝ := fun i => u i 0
/-- Gelfand problem in the ball, multiplicity: the value of a function on the space at the centre of the ball. -/
def gelfandManyCentre (u : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ := u 0
end Checked.Trust.SecondReading
