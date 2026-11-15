import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Real.Basic
/-! Blind literal reading for the monotone segments of the Bonnor–Ebert mass: the closed segment of radii from the centre to the first maximum, and the closed segments between consecutive extrema (from a maximum to the next minimum, from a minimum to the next maximum). Copied verbatim (code) from `runs/2026-11-15T0828Z/be_mono_reader/SecondReadingBEMono.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the claim's own description of the numbering of the extrema; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Set
/-- Bonnor–Ebert sphere: the closed segment of radii from the centre to the first maximum of the mass, for the sequence ξ of extrema. -/
def beRiseFromCentre (ξ : ℕ → ℝ) : Set ℝ := Icc 0 (ξ 0)
/-- Bonnor–Ebert sphere: the closed segment of radii from the (k+1)-th maximum of the mass to the next minimum, for the sequence ξ of extrema. -/
def beFallSegment (ξ : ℕ → ℝ) (k : ℕ) : Set ℝ := Icc (ξ (2 * k)) (ξ (2 * k + 1))
/-- Bonnor–Ebert sphere: the closed segment of radii from the (k+1)-th minimum of the mass to the next maximum, for the sequence ξ of extrema. -/
def beRiseSegment (ξ : ℕ → ℝ) (k : ℕ) : Set ℝ := Icc (ξ (2 * k + 1)) (ξ (2 * k + 2))
end Checked.Trust.SecondReading
