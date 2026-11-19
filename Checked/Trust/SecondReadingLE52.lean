import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index five halves (run 2026-11-19T1628Z): the coefficients of the equation as a first-order system, the centre and central value, the range of the claim, the derived forms of the mass factor and of the central-to-mean density ratio, and the roundings of the first zero, the mass factor and the density ratio computed by the reader. Copied verbatim (code) from `runs/2026-11-19T1628Z/le52_reader/SecondReadingLE52.lean`, written by a blind reader (Sonnet subagent) from the brief committed alone before it in that folder. Source: the reader's own derivation and its own multiprecision computation by two routes; nothing external consulted. -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Lane–Emden index five halves: the right-hand side of φ' (φ = θ') at ξ, as in φ' = this. -/
noncomputable def le52Rhs (θ φ : ℝ → ℝ) (ξ : ℝ) : ℝ := -(2 / ξ * φ ξ) - θ ξ ^ ((5 : ℝ) / 2)
/-- Lane–Emden index five halves: the closed interval from the centre to the end of the claim's range, type written out. -/
def le52RangeTyped : Set ℝ := Icc (0 : ℝ) 6
/-- Lane–Emden index five halves: the same closed interval. -/
def le52Range : Set ℝ := Icc 0 6
/-- Lane–Emden index five halves: the half-open interval after the centre up to the end of the claim's range. -/
def le52RangeOpen : Set ℝ := Ioc (0 : ℝ) 6
/-- Lane–Emden index five halves: the derivative φ is continuous at the centre within the claim's range. -/
def le52ContCentre (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Icc 0 6) 0
/-- Lane–Emden index five halves: the central value of θ. -/
def le52Centre (θ : ℝ → ℝ) : Prop := θ 0 = 1
/-- Lane–Emden index five halves: θ is positive from the centre up to (excluding) x. -/
def le52Before (θ : ℝ → ℝ) (x : ℝ) : Prop := ∀ ξ ∈ Ico 0 x, 0 < θ ξ
/-- Lane–Emden index five halves: the window of the first zero ξ₁. -/
def le52Zero (x : ℝ) : Prop := 5.35527545 ≤ x ∧ x ≤ 5.35527546
/-- Lane–Emden index five halves: the window of the mass factor −ξ₁²θ'(ξ₁) at x. -/
def le52Mass (x : ℝ) (φ : ℝ → ℝ) : Prop := 2.18719956 ≤ -(x ^ 2 * φ x) ∧ -(x ^ 2 * φ x) ≤ 2.18719957
/-- Lane–Emden index five halves: the window of the central concentration ξ₁³/(3 ω) at x. -/
def le52Conc (x : ℝ) (φ : ℝ → ℝ) : Prop := 23.40646222 ≤ x ^ 3 / (3 * -(x ^ 2 * φ x)) ∧ x ^ 3 / (3 * -(x ^ 2 * φ x)) ≤ 23.40646231
end Checked.Trust.SecondReading
