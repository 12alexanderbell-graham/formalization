import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for the limit of the quotient of consecutive deviations of the Bonnor–Ebert mass at its extrema (run 2026-11-25T1628Z). -/
namespace Checked.Trust.SecondReading
open Filter Topology
/-- Bonnor–Ebert sphere: the quotient of the deviations of the pressure-confined mass from the value of the singular isothermal sphere at the next and at the current extremum tends to minus the exponential of minus pi over the square root of the integer of the linearisation. -/
def beTurnRatio (w φ : ℝ → ℝ) (ξ : ℕ → ℝ) : Prop :=
  Tendsto (fun k : ℕ =>
    (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
        Real.sqrt (2 / Real.pi)) /
      (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
        Real.sqrt (2 / Real.pi))) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7))))
end Checked.Trust.SecondReading
