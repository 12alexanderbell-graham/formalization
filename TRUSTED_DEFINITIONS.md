# TRUSTED DEFINITIONS

Every `def`, `structure` or `class` the program writes: what it is meant to capture, and the tests showing it behaves correctly on known examples (annex 40.5). Prefer Mathlib and Physlib definitions.

| Definition | Meant to capture | Mirrors | Tests (Work/Cosmography/LookbackAudit.lean) |
|---|---|---|---|
| `Checked.Cosmography.hubble a t := deriv a t / a t` | Hubble parameter H = ȧ/a | Physlib `Cosmology.FLRW.hubbleConstant` (same formula) | `hubble_exp` (de Sitter: 1), `hubble_sq` (a = t², t=1: 2 = n/t) |
| `Checked.Cosmography.decel a t := -(deriv (deriv a) t * a t) / deriv a t ^ 2` | deceleration q = −äa/ȧ² | Physlib `decelerationParameter` (same formula) | `decel_exp` (−1), `decel_sq` (−1/2 = (1−n)/n); `decel_eq_blind` (= Visser's −(ä/a)H⁻²) |
| `Checked.Cosmography.redshift a t₀ t := a t₀ / a t - 1` | 1 + z = a(t₀)/a(t) | Physlib `FLRW.redshift` (same formula) | used in `lookback_deSitter` (z = e^{−t} − 1) |
| `Checked.Cosmography.Aviles.cosmoCoeff n a t := iteratedDeriv n a t / (a t * hubble a t ^ n)` | a⁽ⁿ⁾/(aHⁿ): j, s, l, m for n = 3…6 (Aviles et al. Eq. 3; Visser's jerk/snap) | none in Physlib | `l0_eds` = 35/2, `m0_eds` = −455/4 (a = t^{2/3}, direct Pochhammer computation); de Sitter `exp`: l₀ = m₀ = 1 (AvilesAudit) |
| `Checked.Cosmography.Aviles.IsFlatLCDM Ω a t₀` | H = H₀√(Ω(1+z)³ + 1 − Ω) near t₀, H₀ = H(t₀) > 0, a > 0 and differentiable near t₀ | Aviles et al. text before Eq. 15 | satisfied by EdS (Ω = 1), de Sitter (Ω = 0), sinh^{2/3} (Ω = sech²t₀); blind restater's `FlatLCDM` implies it (`BlindC2.toOurs`) |

Junk: `deriv` of a non-differentiable function is 0 and `x/0 = 0`; every theorem using these assumes the derivatives exist and a(t₀), ȧ(t₀) ≠ 0.
