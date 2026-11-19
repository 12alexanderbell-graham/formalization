import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index four (reader: independent blind reader 2; derivation, computation and sources: own derivation of θ'' + (2/ξ)θ' + θ⁴ = 0 with θ(0) = 1, own mpmath computation (series start near the centre plus Taylor-series ODE integration at 40 and 55 digits, agreeing to about 35 digits); no tables or web pages used). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Lane–Emden index four: the right-hand side of φ' (φ = θ') at ξ, as in φ' = this. -/
noncomputable def le4Rhs (θ φ : ℝ → ℝ) (ξ : ℝ) : ℝ := -(2 / ξ * φ ξ) - θ ξ ^ 4
/-- Lane–Emden index four: the closed interval from the centre to the end of the claim's range, type written out. -/
def le4RangeTyped : Set ℝ := Icc (0 : ℝ) 16
/-- Lane–Emden index four: the same closed interval. -/
def le4Range : Set ℝ := Icc 0 16
/-- Lane–Emden index four: the half-open interval after the centre up to the end of the claim's range. -/
def le4RangeOpen : Set ℝ := Ioc (0 : ℝ) 16
/-- Lane–Emden index four: the derivative φ is continuous at the centre within the claim's range. -/
def le4ContCentre (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Icc 0 16) 0
/-- Lane–Emden index four: the central value of θ. -/
def le4Centre (θ : ℝ → ℝ) : Prop := θ 0 = 1
/-- Lane–Emden index four: θ is positive from the centre up to (excluding) x. -/
def le4Before (θ : ℝ → ℝ) (x : ℝ) : Prop := ∀ ξ ∈ Ico 0 x, 0 < θ ξ
/-- Lane–Emden index four: the window of the first zero ξ₁. -/
def le4Zero (x : ℝ) : Prop := 14.97154634 ≤ x ∧ x ≤ 14.97154636
/-- Lane–Emden index four: the window of the mass factor −ξ₁²θ'(ξ₁) at x. -/
def le4Mass (x : ℝ) (φ : ℝ → ℝ) : Prop := 1.79722991 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 1.79722992
/-- Lane–Emden index four: the window of the central concentration ξ₁³/(3 ω) at x. -/
def le4Conc (x : ℝ) (φ : ℝ → ℝ) : Prop := 622.407879 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 622.407886
end Checked.Trust.SecondReading
