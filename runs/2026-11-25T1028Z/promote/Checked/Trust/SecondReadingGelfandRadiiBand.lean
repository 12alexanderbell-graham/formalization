import Mathlib.Data.Real.Basic
/-! Blind literal reading for a two-sided band on the quotient of consecutive turning radii of the radial Gelfand branch (run 2026-11-25T1028Z). -/
namespace Checked.Trust.SecondReading
/-- Radial Gelfand problem: the quotient of the next turning radius over the current one lies between `lo` and `hi`. -/
def gelfandRadiiBand (ζ : ℕ → ℝ) (k : ℕ) (lo hi : ℝ) : Prop :=
  lo ≤ ζ (k + 1) / ζ k ∧ ζ (k + 1) / ζ k ≤ hi
end Checked.Trust.SecondReading
