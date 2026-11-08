import Mathlib.Data.Real.Basic
/-! Blind literal reading of two velocity-profile conditions for stagnation-point boundary layers (run 2026-11-08T1228Z): the absolute bound of the streamwise velocity by the outer speed, and the forward velocity strictly below the outer speed, as conditions on the ratio of the two. Copied verbatim (code) from `runs/2026-11-08T1228Z/bound_reader/SecondReadingBound.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own translation of the conditions in words; nothing external consulted. -/
namespace Checked.Trust.SecondReading
/-- Stagnation-point boundary layers: at height η the streamwise velocity is, in absolute value, at most the outer speed (p η is the ratio u / U). -/
def stagSpeedBounded (p : ℝ → ℝ) (η : ℝ) : Prop := -1 ≤ p η ∧ p η ≤ 1
/-- Stagnation-point boundary layers: at height η the streamwise velocity is not negative and strictly below the outer speed (p η is the ratio u / U). -/
def stagForwardBelow (p : ℝ → ℝ) (η : ℝ) : Prop := 0 ≤ p η ∧ p η < 1
end Checked.Trust.SecondReading
