import Mathlib

/-!
# Rigorous simulation of a chemical reaction network (THE RESULT parts 1 and 5): the
# half-conversion time of the full Michaelis–Menten mechanism, certified

**Question.** The Michaelis–Menten mechanism E + S ⇌ C → E + P (rate constants k₁ forward,
k₋₁ backward, k₂ catalytic) under mass-action kinetics is the basic model of enzyme catalysis.
Its full (not quasi-steady-state) rate equations have no closed-form solution. With
k₁ = k₋₁ = k₂ = 1 and initial concentrations [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0 (units: [S]₀ for
concentrations, 1/k₂ for time) the enzyme is *not* in excess-substrate conditions, so the
quasi-steady-state (Briggs–Haldane) approximation is not reliable; the half-conversion time
of the product, t½ with [P](t½) = [S]₀/2, must be computed from the full equations.
Floating-point integration (mpmath Taylor, 30 digits) gives t½ ≈ 2.566514530. This file states
it as a theorem about *every* solution of the rate equations.

**What is stated here** (frozen before proof, annex 40.1):
1. `mm_half_conversion`: every solution of the mass-action rate equations on [0, 13/5]
   (derivatives within the interval) with these rate constants and initial values has
   [P](t) < 1/2 at every t ∈ [0, 2.5665] and [P](2.5666) > 1/2; hence (continuity and the
   intermediate value theorem) the product first reaches half conversion between 2.5665
   and 2.5666.
2. `mm_solution_exists`: such a solution exists (so 1. is not vacuous).

Conventions: `IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` (km₁ = k₋₁) means the four concentration
functions s = [S], e = [E], c = [C], p = [P] take the initial values s₀, e₀, c₀, p₀ at t = 0 and
at every t ∈ [0, T] have derivatives *within* [0, T] (one-sided at the endpoints)
  s′ = −k₁ e s + k₋₁ c,  e′ = −k₁ e s + (k₋₁ + k₂) c,  c′ = k₁ e s − (k₋₁ + k₂) c,  p′ = k₂ c.
No positivity, conservation law or quasi-steady-state assumption is built in: conservation
(e + c and s + c + p constant) follows from the equations.
-/

namespace Work.Sim.MichaelisMenten
open Set

/-- `IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` (km₁ = k₋₁): the concentrations s = [S] (substrate),
e = [E] (free enzyme), c = [C] (enzyme–substrate complex), p = [P] (product) solve the
mass-action rate equations of the Michaelis–Menten mechanism E + S ⇌ C → E + P with forward,
backward and catalytic rate constants k₁, k₋₁, k₂ on the time interval [0, T]: initial values
s₀, e₀, c₀, p₀ at t = 0, and at every t ∈ [0, T] derivatives within [0, T]
s′ = −k₁ e s + k₋₁ c, e′ = −k₁ e s + (k₋₁ + k₂) c, c′ = k₁ e s − (k₋₁ + k₂) c, p′ = k₂ c. -/
def IsMMSolution (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) : Prop :=
  s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀ ∧ ∀ t ∈ Icc 0 T,
    HasDerivWithinAt s (-k₁ * e t * s t + km₁ * c t) (Icc 0 T) t ∧
    HasDerivWithinAt e (-k₁ * e t * s t + (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt c (k₁ * e t * s t - (km₁ + k₂) * c t) (Icc 0 T) t ∧
    HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t

/-- Certified half-conversion time of the full Michaelis–Menten mechanism with
k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0: every solution of the mass-action rate
equations on the time interval [0, 13/5] (derivatives within the interval) has product
concentration strictly below 1/2 at all times in [0, 2.5665] and strictly above 1/2 at time
2.5666, so half of the substrate is first converted to product between 2.5665 and 2.5666. -/
theorem mm_half_conversion {s e c p : ℝ → ℝ} (h : IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p) :
    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧ 1 / 2 < p (25666 / 10000) := by
  sorry

/-- There is a solution of the mass-action rate equations of the Michaelis–Menten mechanism
with k₁ = k₋₁ = k₂ = 1, [S]₀ = [E]₀ = 1, [C]₀ = [P]₀ = 0 on the time interval [0, 13/5]
(derivatives within the interval). -/
theorem mm_solution_exists :
    ∃ s e c p : ℝ → ℝ, IsMMSolution 1 1 1 1 1 0 0 (13 / 5) s e c p := by
  sorry

end Work.Sim.MichaelisMenten
