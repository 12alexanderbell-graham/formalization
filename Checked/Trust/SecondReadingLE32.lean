import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index three halves (run 2026-11-19T1028Z): the coefficients of the equation as a first-order system, the centre and central value, the range of the claim, the derived forms of the mass factor and of the central-to-mean density ratio, and the roundings of the first zero, the mass factor and the density ratio computed by the reader. Copied verbatim (code) from `runs/2026-11-19T1028Z/le32_reader2/SecondReadingLE32.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder (code identical to the first reading in `le32_reader`). Source: the reader's own derivation and its own multiprecision computation at two precisions; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Lane–Emden index three halves: the right-hand side of φ' (φ = θ') at ξ, as in φ' = this. -/
noncomputable def le32Rhs (θ φ : ℝ → ℝ) (ξ : ℝ) : ℝ := -(2 / ξ * φ ξ) - θ ξ ^ ((3 : ℝ) / 2)
/-- Lane–Emden index three halves: the closed interval from the centre to the end of the claim's range, type written out. -/
def le32RangeTyped : Set ℝ := Icc (0 : ℝ) 4
/-- Lane–Emden index three halves: the same closed interval. -/
def le32Range : Set ℝ := Icc 0 4
/-- Lane–Emden index three halves: the half-open interval after the centre up to the end of the claim's range. -/
def le32RangeOpen : Set ℝ := Ioc (0 : ℝ) 4
/-- Lane–Emden index three halves: the derivative φ is continuous at the centre within the claim's range. -/
def le32ContCentre (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Icc 0 4) 0
/-- Lane–Emden index three halves: the central value of θ. -/
def le32Centre (θ : ℝ → ℝ) : Prop := θ 0 = 1
/-- Lane–Emden index three halves: θ is positive from the centre up to (excluding) x. -/
def le32Before (θ : ℝ → ℝ) (x : ℝ) : Prop := ∀ ξ ∈ Ico 0 x, 0 < θ ξ
/-- Lane–Emden index three halves: the window of the first zero ξ₁. -/
def le32Zero (x : ℝ) : Prop := 3.65375373 ≤ x ∧ x ≤ 3.65375374
/-- Lane–Emden index three halves: the window of the mass factor −ξ₁²θ'(ξ₁) at x. -/
def le32Mass (x : ℝ) (φ : ℝ → ℝ) : Prop := 2.71405511 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 2.71405513
/-- Lane–Emden index three halves: the window of the central concentration ξ₁³/(3 ω) at x. -/
def le32Conc (x : ℝ) (φ : ℝ → ℝ) : Prop := 5.99070450 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 5.99070453
end Checked.Trust.SecondReading
