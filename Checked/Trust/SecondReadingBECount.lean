import Mathlib.Data.Real.Basic
/-! Blind literal reading for the number of Bonnor–Ebert spheres of a given mass: the radii of the first minimum, second maximum, second minimum and third maximum in the sequence of extrema, the index of the next-but-one minimum, and the number of spheres in every band of masses and at every extreme value. Copied verbatim (code) from `runs/2026-11-18T1628Z/be_count_reader/SecondReadingBECount.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the claim's own description of the extrema and of the count; nothing external consulted. -/
namespace Checked.Trust.SecondReading
/-- Bonnor–Ebert sphere: the radius of the first minimum of the mass, for the sequence ξ of extrema. -/
def beFirstMinRadius (ξ : ℕ → ℝ) : ℝ := ξ 1
/-- Bonnor–Ebert sphere: the radius of the second maximum of the mass, for the sequence ξ of extrema. -/
def beSecondMaxRadius (ξ : ℕ → ℝ) : ℝ := ξ 2
/-- Bonnor–Ebert sphere: the radius of the second minimum of the mass, for the sequence ξ of extrema. -/
def beSecondMinRadius (ξ : ℕ → ℝ) : ℝ := ξ 3
/-- Bonnor–Ebert sphere: the radius of the third maximum of the mass, for the sequence ξ of extrema. -/
def beThirdMaxRadius (ξ : ℕ → ℝ) : ℝ := ξ 4
/-- Bonnor–Ebert sphere: the index of the (k+2)-th minimum of the mass in the sequence of extrema. -/
def beNextMinIndex (k : ℕ) : ℕ := 2 * k + 3
/-- Bonnor–Ebert sphere: the number of spheres of a mass strictly above the first maximum value. -/
def beCountAboveCritical : ℕ := 0
/-- Bonnor–Ebert sphere: the number of spheres of a mass strictly between the value at the (k+2)-th maximum and the value at the (k+1)-th maximum. -/
def beCountFallBand (k : ℕ) : ℕ := 2 * k + 2
/-- Bonnor–Ebert sphere: the number of spheres of a mass equal to the value at the (k+2)-th maximum. -/
def beCountAtMax (k : ℕ) : ℕ := 2 * k + 3
/-- Bonnor–Ebert sphere: the number of spheres of a mass equal to the value at the (k+1)-th minimum. -/
def beCountAtMin (k : ℕ) : ℕ := 2 * k + 2
/-- Bonnor–Ebert sphere: the number of spheres of a mass strictly between the value at the (k+1)-th minimum and the value at the (k+2)-th minimum. -/
def beCountRiseBand (k : ℕ) : ℕ := 2 * k + 3
/-- Bonnor–Ebert sphere: the number of spheres of a positive mass strictly below the value at the first minimum. -/
def beCountBelowFirstMin : ℕ := 1
end Checked.Trust.SecondReading
