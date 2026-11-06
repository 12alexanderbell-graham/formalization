import Mathlib.Analysis.SpecialFunctions.Exp
/-! Blind literal reading of the radial Gelfand problem in the three-dimensional ball (reader: Claude subagent; derivation and sources: own derivation from the radial Laplacian u'' + (2/r) u' in three dimensions, no external sources consulted). -/
namespace Checked.Trust.SecondReading
open Set
/-- Radial Gelfand problem in the 3-D ball, scaled form: the right-hand side of φ' where φ = w' (so w'' = this expression at s), at a scaled radius s > 0. -/
noncomputable def gelfandRhs (s : ℝ) (w φ : ℝ → ℝ) : ℝ := -(2 / s * φ s) - Real.exp (w s)
/-- Radial Gelfand problem in the 3-D ball: the parameter λ of the solution whose boundary sphere sits at scaled radius s. -/
noncomputable def gelfandLambda (s : ℝ) (w : ℝ → ℝ) : ℝ := s ^ 2 * Real.exp (w s)
/-- Radial Gelfand problem in the 3-D ball: the initial condition on w at the centre (the centre's scaled radius, then the value of w there). -/
def gelfandCentre (w : ℝ → ℝ) : Prop := w 0 = 0
/-- Radial Gelfand problem in the 3-D ball: regularity at the centre, φ = w' continuous at the centre within the radial interval up to S. -/
def gelfandRegular (φ : ℝ → ℝ) (S : ℝ) : Prop := ContinuousWithinAt φ (Icc 0 S) 0
/-- Radial Gelfand problem in the 3-D ball: the closed radial interval from the centre to S. -/
def gelfandDomain (S : ℝ) : Set ℝ := Icc 0 S
/-- Radial Gelfand problem in the 3-D ball: the radial interval from the centre (excluded) to S, where the equation is singular-free. -/
def gelfandPunctured (S : ℝ) : Set ℝ := Ioc 0 S
end Checked.Trust.SecondReading
