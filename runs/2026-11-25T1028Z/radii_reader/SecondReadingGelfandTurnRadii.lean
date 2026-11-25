import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for the growth of consecutive turning radii of the radial Gelfand branch (run 2026-11-25T1028Z). -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Radial Gelfand problem (isothermal sphere): the quotient of the next turning radius over the current one tends to the exponential of an integer times pi over the square root of the integer of the linearisation. -/
def gelfandTurnRadii (ζ : ℕ → ℝ) : Prop :=
  Tendsto (fun k : ℕ => ζ (k + 1) / ζ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7)))
/-- Radial Gelfand problem: a lower bound `lo` on the quotient of consecutive turning radii from the seventh turning point on. -/
def gelfandRadiiFrom (ζ : ℕ → ℝ) (lo : ℝ) : Prop :=
  ∀ k : ℕ, 6 ≤ k → lo ≤ ζ (k + 1) / ζ k
/-- Radial Gelfand problem: the quotient of the deviations of the branch parameter from its value along the singular solution at the next and at the current turning point. -/
noncomputable def gelfandDevQuot (w : ℝ → ℝ) (ζ : ℕ → ℝ) (k : ℕ) : ℝ :=
  (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2)
end Checked.Trust.SecondReading
