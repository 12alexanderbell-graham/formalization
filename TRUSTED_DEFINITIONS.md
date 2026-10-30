# TRUSTED DEFINITIONS

Every `def`, `structure` or `class` the program writes: what it is meant to capture, and the tests showing it behaves correctly on known examples (annex 40.5). Prefer Mathlib and Physlib definitions.

| Definition | Meant to capture | Mirrors | Tests (Work/Cosmography/LookbackAudit.lean) |
|---|---|---|---|
| `Checked.Cosmography.hubble a t := deriv a t / a t` | Hubble parameter H = ȧ/a | Physlib `Cosmology.FLRW.hubbleConstant` (same formula) | `hubble_exp` (de Sitter: 1), `hubble_sq` (a = t², t=1: 2 = n/t) |
| `Checked.Cosmography.decel a t := -(deriv (deriv a) t * a t) / deriv a t ^ 2` | deceleration q = −äa/ȧ² | Physlib `decelerationParameter` (same formula) | `decel_exp` (−1), `decel_sq` (−1/2 = (1−n)/n); `decel_eq_blind` (= Visser's −(ä/a)H⁻²) |
| `Checked.Cosmography.redshift a t₀ t := a t₀ / a t - 1` | 1 + z = a(t₀)/a(t) | Physlib `FLRW.redshift` (same formula) | used in `lookback_deSitter` (z = e^{−t} − 1) |

Junk: `deriv` of a non-differentiable function is 0 and `x/0 = 0`; every theorem using these assumes the derivatives exist and a(t₀), ȧ(t₀) ≠ 0.
