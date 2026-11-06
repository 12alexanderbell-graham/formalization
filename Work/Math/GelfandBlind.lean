import Mathlib

/-! Verbatim copy of the blind restater's file `runs/2026-11-06T1228Z/blind/GelfandBlind.lean`
(run 2026-11-06T1228Z, Sonnet, written without access to the program's statement). -/

namespace Blind.Gelfand

open Real Filter Topology Set

/-- Regular solution `w` of `w'' + (2/s) w' + e^w = 0` on `(0,∞)`, `w(0)=0`, `w'(0)=0`. -/
def IsRegularSol (w : ℝ → ℝ) : Prop :=
  ContinuousOn w (Ici 0) ∧ w 0 = 0 ∧
  HasDerivWithinAt w 0 (Ici 0) 0 ∧
  Tendsto (deriv w) (𝓝[>] 0) (𝓝 0) ∧
  ∀ s > 0, DifferentiableAt ℝ w s ∧ DifferentiableAt ℝ (deriv w) s ∧
    deriv (deriv w) s + 2 / s * deriv w s + Real.exp (w s) = 0

theorem gelfand_critical (w : ℝ → ℝ) (hw : IsRegularSol w) :
    ∃ s₁ ∈ Icc (4.071496844 : ℝ) 4.071496845,
      IsGreatest ((fun s => s ^ 2 * Real.exp (w s)) '' Ioi 0) (s₁ ^ 2 * Real.exp (w s₁)) ∧
      s₁ ^ 2 * Real.exp (w s₁) ∈ Icc (3.321992118 : ℝ) 3.321992119 := by
  sorry

end Blind.Gelfand
