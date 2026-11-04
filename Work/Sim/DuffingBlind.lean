import Mathlib

/-!
# Quarter period of the undamped, unforced Duffing oscillator (blind restatement)

ODE: `x'' + x + x^3 = 0`, `x(0) = 1`, `x'(0) = 0`.

Claim: every solution on `[0, 1.2]` is strictly positive on `[0, 1.192005]` and
strictly negative at `t = 1.192006`; hence its first zero lies in
`(1.192005, 1.192006)`. Such a solution exists on `[0, 1.2]`.
-/

namespace Work.Sim.DuffingBlind

open Set

/-- Lower bound of the quarter-period enclosure, `1.192005`. -/
noncomputable def tLo : ℝ := 1192005 / 1000000

/-- Upper bound of the quarter-period enclosure, `1.192006`. -/
noncomputable def tHi : ℝ := 1192006 / 1000000

/-- The time horizon `1.2`. -/
noncomputable def horizon : ℝ := 6 / 5

/-- `x` solves the Duffing IVP `x'' + x + x^3 = 0`, `x 0 = 1`, `x' 0 = 0` on `[0, T]`.

Modelling choice: we write the second-order ODE as the first-order system
`x' = v`, `v' = -x - x^3`, with an explicit velocity function `v`, and use
`HasDerivWithinAt _ _ (Icc 0 T) t` at every `t ∈ [0, T]`.
* `HasDerivWithinAt` asserts that the derivative actually exists (no junk-value
  issue as with `deriv`, which returns `0` at non-differentiable points, so a
  statement like `deriv (deriv x) t + x t + x t ^ 3 = 0` could be satisfied by
  non-solutions).
* Taking derivatives within `Icc 0 T` gives the correct one-sided derivatives at
  the endpoints `0` and `T`, and does not constrain `x` outside `[0, T]`.
* Existence of `v` with `x' = v` and `v` differentiable is exactly "x is twice
  differentiable on `[0, T]` (within the interval)", with `v` its first
  derivative; the initial velocity condition is `v 0 = 0`. -/
def SolvesIVP (T : ℝ) (x : ℝ → ℝ) : Prop :=
  ∃ v : ℝ → ℝ,
    x 0 = 1 ∧ v 0 = 0 ∧
    (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt x (v t) (Icc 0 T) t) ∧
    (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (-(x t) - (x t) ^ 3) (Icc 0 T) t)

/-- Main claim: any solution on `[0, 1.2]` is strictly positive on `[0, 1.192005]`
and strictly negative at `1.192006`. -/
theorem pos_then_neg (x : ℝ → ℝ) (hx : SolvesIVP horizon x) :
    (∀ t ∈ Icc (0 : ℝ) tLo, 0 < x t) ∧ x tHi < 0 := by
  sorry

/-- Existence: there is a solution on `[0, 1.2]` (so `pos_then_neg` is not vacuous). -/
theorem exists_solution : ∃ x : ℝ → ℝ, SolvesIVP horizon x := by
  sorry

/-- Corollary: the first zero (quarter period) of any solution on `[0, 1.2]`
lies strictly between `1.192005` and `1.192006`: there is a zero `τ` in that open
interval, and `x` is strictly positive on `[0, τ)`, so `τ` is the first zero
in `[0, 1.2]`. -/
theorem first_zero_mem (x : ℝ → ℝ) (hx : SolvesIVP horizon x) :
    ∃ τ ∈ Ioo tLo tHi, x τ = 0 ∧ ∀ t ∈ Ico (0 : ℝ) τ, 0 < x t := by
  sorry

/-- Corollary in "unique first zero" form: there is exactly one `τ ∈ [0, 1.2]` that
is a zero of `x` with `x > 0` on `[0, τ)`, and it lies in `(1.192005, 1.192006)`. -/
theorem first_zero_unique (x : ℝ → ℝ) (hx : SolvesIVP horizon x) :
    ∃! τ, τ ∈ Icc (0 : ℝ) horizon ∧ x τ = 0 ∧ (∀ t ∈ Ico (0 : ℝ) τ, 0 < x t) ∧
      τ ∈ Ioo tLo tHi := by
  sorry

end Work.Sim.DuffingBlind
