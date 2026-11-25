import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-! Blind literal reading for explicit bounds on the quotients of consecutive extrema of the Bonnor–Ebert mass (run 2026-11-25T2228Z). -/
namespace Checked.Trust.SecondReading
/-- Bonnor–Ebert sphere: a lower bound `lo` on the quotient of consecutive extremum radii from the sixth extremum on. -/
def beRadiiFrom (ξ : ℕ → ℝ) (lo : ℝ) : Prop :=
  ∀ k : ℕ, 5 ≤ k → lo ≤ ξ (k + 1) / ξ k
/-- Bonnor–Ebert sphere: the quotient of the next extremum radius over the current one lies between `lo` and `hi`. -/
def beRadiiBand (ξ : ℕ → ℝ) (k : ℕ) (lo hi : ℝ) : Prop :=
  lo ≤ ξ (k + 1) / ξ k ∧ ξ (k + 1) / ξ k ≤ hi
/-- Bonnor–Ebert sphere: the quotient of the deviations of the pressure-confined mass from the value of the singular isothermal sphere at the next and at the current extremum. -/
noncomputable def beDevQuot (w φ : ℝ → ℝ) (ξ : ℕ → ℝ) (k : ℕ) : ℝ :=
  (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
      Real.sqrt (2 / Real.pi)) /
    (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
      Real.sqrt (2 / Real.pi))
end Checked.Trust.SecondReading
