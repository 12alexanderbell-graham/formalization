import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index seven halves (run 2026-11-19T2228Z): the coefficients of the equation as a first-order system, the centre and central value, the range of the claim, the derived forms of the mass factor and of the central-to-mean density ratio, and the roundings of the first zero, the mass factor and the density ratio computed by the reader. Copied verbatim (code) from `runs/2026-11-19T2228Z/le72_reader/SecondReadingLE72.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own derivation and its own multiprecision computation by two routes; nothing external consulted. -/
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
