import Mathlib

/-!
# Lookback time to second order in redshift (target 1, milestone 1)

Conventions (annex XLI):
* Cosmic time `t : ℝ`, observation time `t₀`. Scale factor `a : ℝ → ℝ`. Units: any; `c` does
  not appear (lookback time is a time).
* `H₀ = a'(t₀) / a(t₀)` (Physlib `Cosmology.FLRW.hubbleConstant`).
* `q₀ = -(a''(t₀) a(t₀)) / a'(t₀)²` (Physlib `Cosmology.FLRW.decelerationParameter`).
* Redshift of a source emitting at `t`: `z(t) = a(t₀) / a(t) - 1` (Physlib `FLRW.redshift`).
* `deriv` of a non-differentiable function is junk (`0`); every derivative used is assumed to
  exist.

Model assumptions as hypotheses: `a` is differentiable near `t₀`, `a'` is differentiable at
`t₀` (Physlib's `FLRW` structure assumes the same on its open interval), `a(t₀) ≠ 0`,
`a'(t₀) ≠ 0` (i.e. `H₀ ≠ 0`). No field equations are used: the statement is kinematic.

Source: Physlib `Physlib/Cosmology/FLRW/Distances.lean` TODO ("prove its model-independent
expansion `t₀ - t = H₀⁻¹ [z - ½(2 + q₀) z² + …]`"); M. Visser, "Cosmography: Cosmology
without the Einstein equations", Gen. Rel. Grav. 37 (2005) 1541, arXiv:gr-qc/0411131,
Eq. (11) with `D = c Δt` (Eq. (7)).

Reading of "+ …" (Underspecified, recorded in the audit): with only two derivatives of `a`
the remainder is `o(z²)` (Peano form). The `O(z³)` form under three derivatives is a separate
statement.
-/

namespace Work.Cosmography

open Filter Asymptotics Topology

/-- Hubble parameter at `t`: `a'(t) / a(t)`. Mirrors Physlib `hubbleConstant`. -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Deceleration parameter at `t`: `-(a''(t) a(t)) / a'(t)²`. Mirrors Physlib
`decelerationParameter`. -/
noncomputable def decel (a : ℝ → ℝ) (t : ℝ) : ℝ := -(deriv (deriv a) t * a t) / deriv a t ^ 2

/-- Redshift at observation time `t₀` of a source emitting at `t`: `a(t₀)/a(t) - 1`.
Mirrors Physlib `FLRW.redshift`. -/
noncomputable def redshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- **Milestone 1 (FROZEN statement).** The lookback time `t₀ - t` of a source with redshift
`z = z(t)` satisfies `t₀ - t = H₀⁻¹ (z - (1 + q₀/2) z²) + o(z²)` as `t → t₀`. -/
theorem lookback_second_order (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) := by
  sorry

end Work.Cosmography
