import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for the limit of the quotient of consecutive turning-value deviations of the radial Gelfand branch (run 2026-11-25T0428Z). -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Radial Gelfand problem (isothermal sphere): the quotient of the deviations of the branch parameter from its value along the singular solution at the next and at the current turning point tends to minus the exponential of minus pi over the square root of the integer of the linearisation. -/
def gelfandTurnRatio (w : ℝ → ℝ) (ζ : ℕ → ℝ) : Prop :=
  Tendsto (fun k : ℕ => (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) /
    (ζ k ^ 2 * Real.exp (w (ζ k)) - 2)) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7))))
end Checked.Trust.SecondReading
