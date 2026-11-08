# Brief: blind literal reading of the Lane–Emden problem of index two (run 2026-11-08T0228Z)

You are an independent reader. Do not read anything in /home/claude/formalization except this brief and the output path below; in particular never open `Checked/`, `Work/`, `_archive/`, `runs/` (other than this folder), `scripts/`, `validation/`, `.lake/` or any `*.md` there, and do not use git to look at history.

## The problem

A polytropic star (pressure P = K ρ^(1 + 1/n)) of polytropic index n = 2 in hydrostatic equilibrium. In Emden's variables (ρ = ρ_c θⁿ, r = α ξ with the usual scale α, ξ = 0 at the centre) the structure equation is the Lane–Emden equation of index n, with the regular central conditions. Classical tables of polytropes list, for each n, the first zero ξ₁ of θ (the surface), the dimensionless mass ω_n = ∫₀^ξ₁ ξ² θⁿ dξ, and the ratio of the central density to the mean density of the star.

Jobs:

1. **Derive** the Lane–Emden equation of index two written as a first-order system θ' = φ, φ' = (right-hand side), and put the right-hand side in the shape `-(A / ξ * φ ξ) - θ ξ ^ B` (A, B plain integer numerals; signs are the operators shown). Give the centre Z (value of ξ at the centre) and the central value C = θ(Z) (plain integer numerals). **Derive** ω_n in terms of ξ₁ and θ'(ξ₁) in the shape `-(x ^ P * φ x)` (x = ξ₁, φ x = θ'(ξ₁)), and the central-to-mean density ratio in terms of ξ₁ and ω_n in the shape `x ^ K / (K * ω)` (P, K plain integer numerals).

2. **Compute yourself** (do not look the values up) ξ₁, ω₂ and the density ratio for index two to at least 25 significant digits, by two independent routes (e.g. Python `mpmath` at two precisions, a series start near the centre and a second integration method). Estimate your error.

3. **Round** as follows, writing each result as a plain decimal: L1 = the largest integer multiple of 10⁻¹⁰ not exceeding ξ₁ and U1 = L1 + 10⁻¹⁰ (ten digits after the point); L2 = the largest integer multiple of 2·10⁻¹⁰ not exceeding ω₂ and U2 = L2 + 2·10⁻¹⁰ (ten digits after the point); L3 = the largest integer multiple of 4·10⁻⁹ not exceeding the density ratio and U3 = L3 + 4·10⁻⁹ (nine digits after the point). D = the smallest integer not below ξ₁ + 1/2 (the end of the range on which the claim considers solutions). If your error estimate does not decide a rounding, say so.

4. **Fill in the template below.**

Scripts and scratch files go to a temporary directory outside the repository (e.g. /tmp/le2_reader). Web access: a failed, blocked or timed-out WebFetch/WebSearch is recorded as "not read" — never fetch the same content with curl, wget or code; for arXiv only arxiv.org/abs or arxiv.org/pdf, never ar5iv or e-print. Do not take the numbers from any web page or book: the point is an independent computation.

## What to write

ONE Lean 4 file `runs/2026-11-08T0228Z/le2_reader/SecondReadingLE2.lean`, with exactly the template below. Replace each capital placeholder by your numeral (A, B, Z, C, D, P, K plain integer numerals; L1, U1, L2, U2, L3, U3 plain decimals as in job 3; a placeholder that occurs several times gets the same numeral each time). Nothing else changes: keep every other token, the parentheses and the order exactly as shown (`0` in `0 < θ ξ`, and the binder names, are not placeholders).

```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousOn
/-! Blind literal reading of the Lane–Emden problem of index two (reader: <you>; derivation, computation and sources: <what you used>). -/
namespace Checked.Trust.SecondReading
open Set Filter Topology
/-- Lane–Emden index two: the right-hand side of φ' (φ = θ') at ξ, as in φ' = this. -/
noncomputable def le2Rhs (θ φ : ℝ → ℝ) (ξ : ℝ) : ℝ := -(A / ξ * φ ξ) - θ ξ ^ B
/-- Lane–Emden index two: the closed interval from the centre to the end of the claim's range, type written out. -/
def le2RangeTyped : Set ℝ := Icc (Z : ℝ) D
/-- Lane–Emden index two: the same closed interval. -/
def le2Range : Set ℝ := Icc Z D
/-- Lane–Emden index two: the half-open interval after the centre up to the end of the claim's range. -/
def le2RangeOpen : Set ℝ := Ioc (Z : ℝ) D
/-- Lane–Emden index two: the derivative φ is continuous at the centre within the claim's range. -/
def le2ContCentre (φ : ℝ → ℝ) : Prop := ContinuousWithinAt φ (Icc Z D) Z
/-- Lane–Emden index two: the central value of θ. -/
def le2Centre (θ : ℝ → ℝ) : Prop := θ Z = C
/-- Lane–Emden index two: θ is positive from the centre up to (excluding) x. -/
def le2Before (θ : ℝ → ℝ) (x : ℝ) : Prop := ∀ ξ ∈ Ico Z x, 0 < θ ξ
/-- Lane–Emden index two: the window of the first zero ξ₁. -/
def le2Zero (x : ℝ) : Prop := L1 ≤ x ∧ x ≤ U1
/-- Lane–Emden index two: the window of the mass factor −ξ₁²θ'(ξ₁) at x. -/
def le2Mass (x : ℝ) (φ : ℝ → ℝ) : Prop := L2 ≤ -(x ^ P * φ x) ∧ -(x ^ P * φ x) ≤ U2
/-- Lane–Emden index two: the window of the central concentration ξ₁³/(3 ω) at x. -/
def le2Conc (x : ℝ) (φ : ℝ → ℝ) : Prop :=
  L3 ≤ x ^ K / (K * -(x ^ P * φ x)) ∧ x ^ K / (K * -(x ^ P * φ x)) ≤ U3
end Checked.Trust.SecondReading
```

No other definitions and no comments other than the module doc and the docstrings above (fill in the module doc's reader/sources/method). If the problem does not fit the template, do not change the shape: say so in the module doc and in your report.

Compile the file with `export PATH=$HOME/.elan/bin:$PATH; cd /home/claude/formalization; lake env lean runs/2026-11-08T0228Z/le2_reader/SecondReadingLE2.lean` (timeout 300000 ms). Do not run `lake build`.

Finally report: every placeholder value; ξ₁, ω₂ and the ratio with all digits you trust, your error estimate and how you got it; what you consulted; anything uncertain.
