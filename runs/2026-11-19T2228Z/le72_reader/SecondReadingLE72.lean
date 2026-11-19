import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index seven halves (reader: independent blind reader subagent; derivation, computation and sources: own derivation of θ'' + (2/ξ)θ' + θ^(7/2) = 0, own mpmath computation by Taylor-method ODE integration from a series start at two precisions and start points, checked with a scipy DOP853 run; no tables or web pages used). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Lane–Emden index seven halves: the right-hand side of φ' (φ = θ') at ξ, as in φ' = this. -/
noncomputable def le72Rhs (θ φ : ℝ → ℝ) (ξ : ℝ) : ℝ := -(2 / ξ * φ ξ) - θ ξ ^ ((7 : ℝ) / 2)
/-- Lane–Emden index seven halves: the closed interval from the centre to the end of the claim's range, type written out. -/
def le72RangeTyped : Set ℝ := Icc (0 : ℝ) 10
/-- Lane–Emden index seven halves: the same closed interval. -/
def le72Range : Set ℝ := Icc 0 10
/-- Lane–Emden index seven halves: the half-open interval after the centre up to the end of the claim's range. -/
def le72RangeOpen : Set ℝ := Ioc (0 : ℝ) 10
/-- Lane–Emden index seven halves: the derivative φ is continuous at the centre within the claim's range. -/
def le72ContCentre (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Icc 0 10) 0
/-- Lane–Emden index seven halves: the central value of θ. -/
def le72Centre (θ : ℝ → ℝ) : Prop := θ 0 = 1
/-- Lane–Emden index seven halves: θ is positive from the centre up to (excluding) x. -/
def le72Before (θ : ℝ → ℝ) (x : ℝ) : Prop := ∀ ξ ∈ Ico 0 x, 0 < θ ξ
/-- Lane–Emden index seven halves: the window of the first zero ξ₁. -/
def le72Zero (x : ℝ) : Prop := 9.53580534 ≤ x ∧ x ≤ 9.53580535
/-- Lane–Emden index seven halves: the window of the mass factor −ξ₁²θ'(ξ₁) at x. -/
def le72Mass (x : ℝ) (φ : ℝ → ℝ) : Prop := 1.89055709 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 1.89055710
/-- Lane–Emden index seven halves: the window of the central concentration ξ₁³/(3 ω) at x. -/
def le72Conc (x : ℝ) (φ : ℝ → ℝ) : Prop := 152.8836627 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 152.8836632
end Checked.Trust.SecondReading
