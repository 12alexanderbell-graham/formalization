import Mathlib

/-!
# Michaelis–Menten half-conversion time (blind restatement)

Mechanism `E + S ⇌ C → E + P` with mass-action kinetics, rate constants
`k₁ = 1` (binding), `k₋₁ = 1` (unbinding), `k₂ = 1` (catalysis).

Reaction fluxes: `v₁ = k₁·e·s` (E + S → C), `v₋₁ = k₋₁·c` (C → E + S),
`v₂ = k₂·c` (C → E + P). Stoichiometry gives

* `s' = -v₁ + v₋₁            = -k₁ e s + k₋₁ c`
* `e' = -v₁ + v₋₁ + v₂       = -k₁ e s + (k₋₁ + k₂) c`
* `c' =  v₁ - v₋₁ - v₂       =  k₁ e s - (k₋₁ + k₂) c`
* `p' =  v₂                  =  k₂ c`

With all constants equal to 1 these become
`s' = -e s + c`, `e' = -e s + 2 c`, `c' = e s - 2 c`, `p' = c`.
Initial values: `s(0) = 1`, `e(0) = 1`, `c(0) = 0`, `p(0) = 0`.
-/

namespace Work.Sim.MMBlind

open Set

/-- `IsMMSolution s e c p T` : the functions `s e c p : ℝ → ℝ` (concentrations of
substrate, free enzyme, complex, product) solve the full four-species mass-action
Michaelis–Menten system with `k₁ = k₋₁ = k₂ = 1` on the closed interval `[0, T]`,
with initial values `s(0)=1, e(0)=1, c(0)=0, p(0)=0`.

Modelling choices:
* **Derivative convention.** On a closed interval the natural textbook reading is
  that each species is differentiable on `[0, T]` with the ODE holding at every
  point, using one-sided derivatives at the endpoints `0` and `T`. This is exactly
  `HasDerivWithinAt f f' (Icc 0 T) t` for every `t ∈ Icc 0 T` (at interior points it
  agrees with the ordinary derivative; at `0` it is the right derivative, at `T`
  the left derivative). It implies continuity on `[0, T]`, so the initial
  condition genuinely constrains the solution.
* **All four species are carried**, with their own equations; the conservation
  laws `e + c = 1` and `s + c + p = 1` are *not* assumed — they follow from the
  equations.
* **Not assumed:** nonnegativity of concentrations, any behaviour outside `[0, T]`
  (values there are irrelevant), any quasi-steady-state approximation, or
  uniqueness (which follows from the local Lipschitz right-hand side). -/
def IsMMSolution (s e c p : ℝ → ℝ) (T : ℝ) : Prop :=
  s 0 = 1 ∧ e 0 = 1 ∧ c 0 = 0 ∧ p 0 = 0 ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt s (-(e t * s t) + c t) (Icc 0 T) t ∧
    HasDerivWithinAt e (-(e t * s t) + 2 * c t) (Icc 0 T) t ∧
    HasDerivWithinAt c (e t * s t - 2 * c t) (Icc 0 T) t ∧
    HasDerivWithinAt p (c t) (Icc 0 T) t

/-- **Claim A.** For every solution of the full mass-action system on `[0, 2.6]`,
the product concentration is strictly below `1/2` at every `t ∈ [0, 2.5665]` and
strictly above `1/2` at `t = 2.5666`. Quantified universally over solutions (no
existence is asserted here; see `claimB`). Constants are exact rationals. -/
theorem claimA (s e c p : ℝ → ℝ) (h : IsMMSolution s e c p (26 / 10)) :
    (∀ t ∈ Icc (0 : ℝ) (25665 / 10000), p t < 1 / 2) ∧
      1 / 2 < p (25666 / 10000) := by
  sorry

/-- **Claim B.** A solution of the full mass-action system with the given initial
values exists on the whole interval `[0, 2.6]` (no blow-up before `2.6`), in the
sense of `IsMMSolution`. Together with `claimA` this rules out vacuity. -/
theorem claimB : ∃ s e c p : ℝ → ℝ, IsMMSolution s e c p (26 / 10) := by
  sorry

end Work.Sim.MMBlind
