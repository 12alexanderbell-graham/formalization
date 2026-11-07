import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
/-! Blind literal reading of the Gelfand problem in the unit ball as a PDE (reader: independent blind reader; derivation, computation and sources: radial reduction u(r) = w(kr) - w(k) with w'' + (2/s) w' + e^w = 0, w(0) = w'(0) = 0, lambda = k^2 e^(w(k)); lambda* = max_s s^2 e^(w(s)) computed with mpmath odefun from a Taylor start at s = 0.1, at 30 and 40 digits (agree to 30 digits), cross-checked with scipy RK; lambda* = 3.32199211833982398841..., attained at s = 4.07149684429813934760...; no web or book sources used). The setting fits the template without change. -/
namespace Checked.Trust.SecondReading
open Metric
/-- Gelfand problem in the ball as a PDE: the space of the problem, Euclidean space of the problem's dimension. -/
def gelfandPdeSpace : Type := EuclideanSpace ℝ (Fin 3)
/-- Gelfand problem in the ball as a PDE: the open ball of the problem (centre, radius). -/
def gelfandPdeBall : Set (EuclideanSpace ℝ (Fin 3)) := ball (0 : EuclideanSpace ℝ (Fin 3)) 1
/-- Gelfand problem in the ball as a PDE: the closed ball of the problem (centre, radius). -/
def gelfandPdeClosedBall : Set (EuclideanSpace ℝ (Fin 3)) := closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1
/-- Gelfand problem in the ball as a PDE: a classical solution is K times continuously differentiable on the open ball. -/
def gelfandPdeRegular (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop := ContDiffOn ℝ 2 u (ball 0 1)
/-- Gelfand problem in the ball as a PDE: a classical solution is continuous on the closed ball. -/
def gelfandPdeContinuous (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop := ContinuousOn u (closedBall 0 1)
/-- Gelfand problem in the ball as a PDE: λ is at most the reader's nine-decimal lower rounding of the critical parameter. -/
def gelfandPdeLamRange (lam : ℝ) : Prop := lam ≤ 3.321992118
end Checked.Trust.SecondReading
