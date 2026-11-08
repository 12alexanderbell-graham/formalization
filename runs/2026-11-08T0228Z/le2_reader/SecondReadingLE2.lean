import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index two (reader: Claude subagent; derivation, computation and sources: own derivation of θ'' + (2/ξ)θ' + θ² = 0, series start at ξ=0.3 and 0.5 plus mpmath Taylor odefun at 40 and 50 digits, cross-checked by scipy DOP853; no tables or web consulted). The problem fits the template. -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Lane–Emden index two: the right-hand side of φ' (φ = θ') at ξ, as in φ' = this. -/
noncomputable def le2Rhs (θ φ : ℝ → ℝ) (ξ : ℝ) : ℝ := -(2 / ξ * φ ξ) - θ ξ ^ 2
/-- Lane–Emden index two: the closed interval from the centre to the end of the claim's range, type written out. -/
def le2RangeTyped : Set ℝ := Icc (0 : ℝ) 5
/-- Lane–Emden index two: the same closed interval. -/
def le2Range : Set ℝ := Icc 0 5
/-- Lane–Emden index two: the half-open interval after the centre up to the end of the claim's range. -/
def le2RangeOpen : Set ℝ := Ioc (0 : ℝ) 5
/-- Lane–Emden index two: the derivative φ is continuous at the centre within the claim's range. -/
def le2ContCentre (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Icc 0 5) 0
/-- Lane–Emden index two: the central value of θ. -/
def le2Centre (θ : ℝ → ℝ) : Prop := θ 0 = 1
/-- Lane–Emden index two: θ is positive from the centre up to (excluding) x. -/
def le2Before (θ : ℝ → ℝ) (x : ℝ) : Prop := ∀ ξ ∈ Ico 0 x, 0 < θ ξ
/-- Lane–Emden index two: the window of the first zero ξ₁. -/
def le2Zero (x : ℝ) : Prop := 4.3528745959 ≤ x ∧ x ≤ 4.3528745960
/-- Lane–Emden index two: the window of the mass factor −ξ₁²θ'(ξ₁) at x. -/
def le2Mass (x : ℝ) (φ : ℝ → ℝ) : Prop := 2.4110460120 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 2.4110460122
/-- Lane–Emden index two: the window of the central concentration ξ₁³/(3 ω) at x. -/
def le2Conc (x : ℝ) (φ : ℝ → ℝ) : Prop :=
  11.402542860 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 11.402542864
end Checked.Trust.SecondReading
