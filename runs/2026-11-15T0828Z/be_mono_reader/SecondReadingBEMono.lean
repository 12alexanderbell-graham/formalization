import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Real.Basic
/-! Blind literal reading for the monotone segments of the Bonnor–Ebert mass (run 2026-11-15T0828Z). -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the closed segment of radii from the centre to the first maximum of the mass, for the sequence ξ of extrema. -/
def beRiseFromCentre (ξ : ℕ → ℝ) : Set ℝ := Icc 0 (ξ 0)
/-- Bonnor–Ebert sphere: the closed segment of radii from the (k+1)-th maximum of the mass to the next minimum, for the sequence ξ of extrema. -/
def beFallSegment (ξ : ℕ → ℝ) (k : ℕ) : Set ℝ := Icc (ξ (2 * k)) (ξ (2 * k + 1))
/-- Bonnor–Ebert sphere: the closed segment of radii from the (k+1)-th minimum of the mass to the next maximum, for the sequence ξ of extrema. -/
def beRiseSegment (ξ : ℕ → ℝ) (k : ℕ) : Set ℝ := Icc (ξ (2 * k + 1)) (ξ (2 * k + 2))
end Checked.Trust.SecondReading
