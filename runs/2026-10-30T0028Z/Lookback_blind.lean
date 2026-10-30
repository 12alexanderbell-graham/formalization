import Mathlib

/-!
# Lookback time: model-independent (cosmographic) expansion to second order in z

Claim (Physlib TODO; Visser, gr-qc/0411131, Eqs. (7), (11)):
  t₀ - t = H₀⁻¹ [ z - (1 + q₀/2) z² ] + O(z³).

Only the kinematics of the scale factor `a : ℝ → ℝ` is used (no field equations).
The redshift `z` is treated as a function of the emission time `t`
(1 + z = a(t₀)/a(t)), and the remainder is expressed as `O(z(t)³)` along the filter
`t → t₀`. Since `dz/dt (t₀) = -H₀ ≠ 0`, `t ↦ z(t)` is a local diffeomorphism near `t₀`
sending `t₀ ↦ 0`, so this is equivalent to the statement "as `z → 0`" for the
(locally defined) inverse `t(z)`; parametrising by `t` avoids constructing that inverse.
-/

namespace LookbackBlind

open Filter Asymptotics

/-- Hubble parameter `H = (1/a) da/dt`. -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Deceleration parameter `q = -(1/a) (d²a/dt²) [(1/a)(da/dt)]⁻²` (Visser's definition). -/
noncomputable def decel (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(deriv (deriv a) t / a t) * (hubble a t)⁻¹ ^ 2

/-- Redshift of light emitted at `t` and received at `t₀`: `1 + z = a(t₀)/a(t)`. -/
noncomputable def redshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- Lookback time `t₀ - t` (light travel time; Visser's `D = c Δt` divided by `c`). -/
def lookback (t₀ t : ℝ) : ℝ := t₀ - t

/-- Second-order cosmographic expansion of the lookback time in powers of the redshift:
`t₀ - t = H₀⁻¹ [z - (1 + q₀/2) z²] + O(z³)` as the emission time `t → t₀`
(equivalently `z → 0`).

Hypotheses:
* `ha : ContDiffAt ℝ 3 a t₀` — `a` is `C³` on a neighbourhood of `t₀`. `C²` is what is
  needed to *define* `q₀`; one more derivative is needed so that the remainder is
  genuinely `O(z³)` (Visser's `O(z²)` inside the braces) rather than merely `o(z²)`.
  This also guarantees that `deriv a` and `deriv (deriv a)` at `t₀` are the true
  derivatives, not Mathlib junk values `0`.
* `ha₀ : 0 < a t₀` — positive scale factor today; makes `H₀`, `q₀`, and (by continuity)
  `z(t)` for `t` near `t₀` free of division-by-zero junk.
* `hH : deriv a t₀ ≠ 0` — `H₀ ≠ 0` (non-static universe). Needed for `H₀⁻¹` and `q₀`
  to be meaningful and for `z ↦ t` to be locally invertible; without it the claim is
  false/junk (e.g. `a` constant gives `z ≡ 0` but `t₀ - t ≠ 0`).
No sign assumption on `H₀` (expanding vs contracting) is needed, and the statement is
two-sided in `t` (it also holds for `t > t₀`, i.e. it is stronger than restricting to
the past `t < t₀`). -/
theorem lookback_expansion (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ContDiffAt ℝ 3 a t₀) (ha₀ : 0 < a t₀) (hH : deriv a t₀ ≠ 0) :
    (fun t => lookback t₀ t
        - (hubble a t₀)⁻¹ * (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2))
      =O[nhds t₀] (fun t => redshift a t₀ t ^ 3) := by
  sorry

end LookbackBlind
