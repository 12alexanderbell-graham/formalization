import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for geometrically shrinking bounds on the quotients of consecutive extrema of the Bonnor–Ebert mass (run 2026-11-26T0428Z, second reader). -/
namespace Checked.Trust.SecondReading
/-- Bonnor–Ebert sphere: the distance of the quotient of consecutive extremum radii from its limit, at the sixth-plus-n extremum, is at most `c₁` times `q` to the power n. -/
def beDecayRadiusBound (ξ : ℕ → ℝ) (n : ℕ) (c₁ q : ℝ) : Prop :=
  |ξ (n + 6) / ξ (n + 5) - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤ c₁ * q ^ n
/-- Bonnor–Ebert sphere: the distance of the quotient of the deviations of the pressure-confined mass from the singular value at consecutive extrema from its limit, at the sixth-plus-n extremum, is at most `c₂` times `q` to the power n. -/
def beDecayDevBound (w φ : ℝ → ℝ) (ξ : ℕ → ℝ) (n : ℕ) (c₂ q : ℝ) : Prop :=
  |(ξ (n + 6) ^ 2 * (-φ (ξ (n + 6))) * Real.exp (w (ξ (n + 6)) / 2) / Real.sqrt (4 * Real.pi) -
        Real.sqrt (2 / Real.pi)) /
      (ξ (n + 5) ^ 2 * (-φ (ξ (n + 5))) * Real.exp (w (ξ (n + 5)) / 2) / Real.sqrt (4 * Real.pi) -
        Real.sqrt (2 / Real.pi)) -
    -Real.exp (-(Real.pi / Real.sqrt 7))| ≤ c₂ * q ^ n
end Checked.Trust.SecondReading
