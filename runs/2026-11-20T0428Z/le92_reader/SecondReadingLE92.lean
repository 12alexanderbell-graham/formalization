import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index nine halves (reader: Claude subagent, blind reader; derivation, computation and sources: own derivation θ'' + (2/ξ)θ' + θ^(9/2) = 0, θ(0) = 1, ω = -ξ₁²θ'(ξ₁), ratio ξ₁³/(3ω); numerics by mpmath Taylor ODE integration at 40 digits from a series start at ξ = 10⁻³ and 10⁻⁴, cross-checked with scipy DOP853; no external sources). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Lane–Emden index nine halves: the right-hand side of φ' (φ = θ') at ξ, as in φ' = this. -/
noncomputable def le92Rhs (θ φ : ℝ → ℝ) (ξ : ℝ) : ℝ := -(2 / ξ * φ ξ) - θ ξ ^ ((9 : ℝ) / 2)
/-- Lane–Emden index nine halves: the closed interval from the centre to the end of the claim's range, type written out. -/
def le92RangeTyped : Set ℝ := Icc (0 : ℝ) 32
/-- Lane–Emden index nine halves: the same closed interval. -/
def le92Range : Set ℝ := Icc 0 32
/-- Lane–Emden index nine halves: the half-open interval after the centre up to the end of the claim's range. -/
def le92RangeOpen : Set ℝ := Ioc (0 : ℝ) 32
/-- Lane–Emden index nine halves: the derivative φ is continuous at the centre within the claim's range. -/
def le92ContCentre (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Icc 0 32) 0
/-- Lane–Emden index nine halves: the central value of θ. -/
def le92Centre (θ : ℝ → ℝ) : Prop := θ 0 = 1
/-- Lane–Emden index nine halves: θ is positive from the centre up to (excluding) x. -/
def le92Before (θ : ℝ → ℝ) (x : ℝ) : Prop := ∀ ξ ∈ Ico 0 x, 0 < θ ξ
/-- Lane–Emden index nine halves: the window of the first zero ξ₁. -/
def le92Zero (x : ℝ) : Prop := 31.836463 ≤ x ∧ x ≤ 31.836464
/-- Lane–Emden index nine halves: the window of the mass factor −ξ₁²θ'(ξ₁) at x. -/
def le92Mass (x : ℝ) (φ : ℝ → ℝ) : Prop := 1.7377988 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 1.7377989
/-- Lane–Emden index nine halves: the window of the central concentration ξ₁³/(3 ω) at x. -/
def le92Conc (x : ℝ) (φ : ℝ → ℝ) : Prop := 6189.4730 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 6189.4733
end Checked.Trust.SecondReading
