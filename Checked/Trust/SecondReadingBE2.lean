import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
/-! Blind literal reading of the radial range of the Bonnor–Ebert decrease claim (run 2026-11-12T0427Z). Copied verbatim (code) from `runs/2026-11-12T0427Z/be_reader2/SecondReadingBE2.lean`, written by a blind reader (Sonnet subagent) from the brief `runs/2026-11-12T0427Z/be_reader/BRIEF2.md` committed alone before it. Source: the claim's own words. -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the closed radial range, from the radius ξ of the maximum to the end stated in the claim, on which the mass decreases. -/
def beDecreaseRange (ξ : ℝ) : Set ℝ := Icc ξ 7
end Checked.Trust.SecondReading
