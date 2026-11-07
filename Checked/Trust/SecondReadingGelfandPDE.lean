import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
/-! Blind literal reading of the Gelfand problem in the unit ball as a PDE (run 2026-11-07T0028Z): the dimension of the space, the centre and radius of the ball, the order of differentiability of a classical solution, and a lower rounding of the critical parameter computed independently by the reader. Copied verbatim (code) from `runs/2026-11-07T0028Z/gelfand_pde_reader/SecondReadingGelfandPDE.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own derivation of the radial reduction and its own high-precision integration; nothing external consulted. -/
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
