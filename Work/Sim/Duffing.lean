import Mathlib

/-!
# Rigorous simulation (THE RESULT part 1, "simulations"): the first zero of the Duffing
# oscillator, certified by a validated ODE enclosure

**Question.** The undamped, unforced Duffing oscillator x'' + k x + β x³ = 0 (the anharmonic
oscillator of every mechanics text; hardening spring for β > 0) has no elementary closed-form
solution. Its period is usually obtained by numerical integration (floating point, no error
bound) or by perturbation series (Lindstedt–Poincaré, truncated). With k = β = 1, x(0) = 1,
x'(0) = 0 the solution is x(t) = cn(√2 t | m = 1/4), whose first zero is
t₁ = K(1/4)/√2 = 1.1920055073… (quarter period; period 4.7680220…).

**What is stated here** (frozen before proof, annex 40.1):
1. `duffing_first_zero`: every solution of x'' + x + x³ = 0, x(0) = 1, x'(0) = 0 on [0, 6/5]
   is strictly positive on [0, 1.192005] and strictly negative at t = 1.192006; hence its
   first zero lies in (1.192005, 1.192006).
2. `duffing_exists`: such a solution exists (so 1. is not vacuous).

**Method (the simulator).** A piecewise polynomial approximate trajectory with rational
coefficients, a certified bound on its defect g′ − F(g) on each cell (exact rational arithmetic),
the Lipschitz constant of F on a box that every solution stays in (energy conservation), and
Grönwall's inequality (Mathlib `dist_le_of_approx_trajectories_ODE_of_mem`) give a proved
enclosure of every true solution. No floating point is trusted.

Conventions: `IsDuffingIVP k β x₀ v₀ T x` means x is differentiable at every t ∈ [0, T] with
derivative v t, v is differentiable there with derivative −k x − β x³, and x 0 = x₀, v 0 = v₀
(two-sided derivatives, so x solves the equation on an open set containing [0, T]).

FROZEN in run 2026-11-04T0628Z before proof work.
-/

namespace Work.Sim.Duffing
open Set

/-- `x` solves the Duffing initial value problem x'' + k·x + β·x³ = 0, x(0) = x₀, x'(0) = v₀ on
the time interval [0, T]: there is a velocity function `v` with x′ = v and v′ = −k·x − β·x³ at
every time in [0, T], and x(0) = x₀, v(0) = v₀. -/
def IsDuffingIVP (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) : Prop :=
  x 0 = x₀ ∧ ∃ v : ℝ → ℝ, v 0 = v₀ ∧
    ∀ t ∈ Icc 0 T, HasDerivAt x (v t) t ∧ HasDerivAt v (-k * x t - β * x t ^ 3) t

/-- First zero of the Duffing oscillator x'' + x + x³ = 0 released from rest at x = 1: every
solution on [0, 6/5] is strictly positive for all times in [0, 1.192005] and strictly negative
at time 1.192006, so its first zero (the quarter period) lies strictly between 1.192005 and
1.192006. -/
theorem duffing_first_zero (x : ℝ → ℝ) (hx : IsDuffingIVP 1 1 1 0 (6 / 5) x) :
    (∀ t ∈ Icc (0 : ℝ) (1192005 / 1000000), 0 < x t) ∧ x (1192006 / 1000000) < 0 := by
  sorry

/-- There is a solution of the Duffing initial value problem x'' + x + x³ = 0, x(0) = 1,
x'(0) = 0 on the time interval [0, 6/5]. -/
theorem duffing_exists : ∃ x : ℝ → ℝ, IsDuffingIVP 1 1 1 0 (6 / 5) x := by
  sorry

end Work.Sim.Duffing
