import Mathlib.Data.Real.Basic
/-! Blind literal reading of two velocity-profile conditions for stagnation-point boundary layers (reader: Claude Sonnet 5.5; reasoning: since u = U * p η with U > 0, |u| ≤ U means -1 ≤ p η ≤ 1 and 0 ≤ u < U means 0 ≤ p η < 1). -/
namespace Checked.Trust.SecondReading
/-- Stagnation-point boundary layers: at height η the streamwise velocity is, in absolute value, at most the outer speed (p η is the ratio u / U). -/
def stagSpeedBounded (p : ℝ → ℝ) (η : ℝ) : Prop := -1 ≤ p η ∧ p η ≤ 1
/-- Stagnation-point boundary layers: at height η the streamwise velocity is not negative and strictly below the outer speed (p η is the ratio u / U). -/
def stagForwardBelow (p : ℝ → ℝ) (η : ℝ) : Prop := 0 ≤ p η ∧ p η < 1
end Checked.Trust.SecondReading
