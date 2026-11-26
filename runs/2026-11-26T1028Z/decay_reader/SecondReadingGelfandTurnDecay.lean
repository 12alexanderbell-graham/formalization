import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for geometrically shrinking bounds on the quotients of consecutive turning points of the radial Gelfand branch (run 2026-11-26T1028Z). -/
namespace Checked.Trust.SecondReading
/-- Radial Gelfand problem: the distance of the quotient of consecutive turning radii from its limit, at the seventh-plus-n turning point, is at most `c₁` times `q` to the power n. -/
def gelfandDecayRadiusBound (ζ : ℕ → ℝ) (n : ℕ) (c₁ q : ℝ) : Prop :=
  |ζ (n + 7) / ζ (n + 6) - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤ c₁ * q ^ n
/-- Radial Gelfand problem: the distance of the quotient of the deviations of the branch parameter from the singular value at consecutive turning points from its limit, at the seventh-plus-n turning point, is at most `c₂` times `q` to the power n. -/
def gelfandDecayDevBound (w : ℝ → ℝ) (ζ : ℕ → ℝ) (n : ℕ) (c₂ q : ℝ) : Prop :=
  |(ζ (n + 7) ^ 2 * Real.exp (w (ζ (n + 7))) - 2) / (ζ (n + 6) ^ 2 * Real.exp (w (ζ (n + 6))) - 2) -
    -Real.exp (-(Real.pi / Real.sqrt 7))| ≤ c₂ * q ^ n
end Checked.Trust.SecondReading
