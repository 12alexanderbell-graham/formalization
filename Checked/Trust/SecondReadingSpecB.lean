/- Copied verbatim (code unchanged) from `runs/2026-11-27T0228Z/specB/SecondReadingSpecB.lean`, written by blind reader B (Sonnet subagent, brief `runs/2026-11-27T0228Z/specB/briefB.md`; it reported reading only the brief, writing from memory with no web source). Agreement with the program's pinned definitions: `Checked/Trust/SpecAgreement.lean`. -/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Checked.Trust.SecondReadingSpecB

/-- Hubble expansion rate `H a t = ȧ(t) / a(t)` (Weinberg, *Cosmology*, §1.5; Hogg 1999, §3).
The specification determines `H a t` at every `t` where `a t ≠ 0` and `a` is differentiable at `t`.
Nothing is said where `a t = 0` or `a` is not differentiable there. -/
structure HubbleSpecB (H : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Defining formula `H = ȧ / a` (Weinberg §1.5), for nonzero scale factor and differentiable `a`. -/
  eq_deriv_div : ∀ (a : ℝ → ℝ) (t : ℝ), a t ≠ 0 → DifferentiableAt ℝ a t →
    H a t = deriv a t / a t

/-- Deceleration parameter `q = - ä a / ȧ² = - ä / (a H²)` (Weinberg §1.5; Visser 2004, gr-qc/0309109).
Determined at every `t` where `a t ≠ 0`, `a` is twice continuously differentiable at `t`, and
`ȧ(t) ≠ 0` (i.e. `H ≠ 0`, otherwise `q` has a vanishing denominator and is not constrained). -/
structure DecelSpecB (Q : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Defining formula `q = - ä(t) a(t) / ȧ(t)²` (equal to `-ä/(aH²)` with `H = ȧ/a`). -/
  eq_formula : ∀ (a : ℝ → ℝ) (t : ℝ), a t ≠ 0 → ContDiffAt ℝ 2 a t → deriv a t ≠ 0 →
    Q a t = - (iteratedDeriv 2 a t * a t) / (deriv a t) ^ 2

/-- Cosmological redshift `z = a(t₀)/a(t) - 1` of light emitted at `t` and observed at `t₀`
(Weinberg §1.2; Hogg 1999, §2: `1 + z = a(t₀)/a(t)`). Determined whenever `t ≤ t₀` and both scale
factors are positive. -/
structure RedshiftSpecB (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- `1 + z = a(t₀) / a(t)` (Weinberg §1.2; Hogg §2), for emission not after observation and
  positive scale factor at both times. -/
  one_add_eq : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → 0 < a t → 0 < a t₀ →
    1 + Z a t₀ t = a t₀ / a t

/-- `n`-th cosmographic coefficient (Aviles–Gruber–Luongo–Quevedo 2012, arXiv:1204.2007, Eq. (3)):
`j = a⁽³⁾/(a H³)`, `s = a⁽⁴⁾/(a H⁴)`, `l = a⁽⁵⁾/(a H⁵)`, i.e. for `n ≥ 3`
`C n = a⁽ⁿ⁾ / (a Hⁿ)` with `H = ȧ/a` (the case `n = 2`, the deceleration parameter, carries an extra
minus sign in the source and is deliberately NOT constrained here, nor `n ≤ 1`).
Determined for `n ≥ 3` at every `t` where `a t ≠ 0`, `a` is `n` times continuously differentiable at
`t` and `ȧ(t) ≠ 0` (so `H ≠ 0`). The sign and normalisation are those of the source's Eq. (3). -/
structure CoeffSpecB (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Pattern `C n = a⁽ⁿ⁾ / (a · Hⁿ)` for `n ≥ 3` with `H = ȧ / a` written out. -/
  eq_pattern : ∀ (n : ℕ) (a : ℝ → ℝ) (t : ℝ), 3 ≤ n → a t ≠ 0 → ContDiffAt ℝ n a t →
    deriv a t ≠ 0 →
    C n a t = iteratedDeriv n a t / (a t * (deriv a t / a t) ^ n)

/-- The y-redshift of Cattoën–Visser 2007 (gr-qc/0703122), as used in Bamba–Capozziello–Nojiri–Odintsov
2012 (arXiv:1205.3421, §10): `y = 1 - a(t)/a(t₀) = z/(1+z)` where `z = a(t₀)/a(t) - 1`.
Determined whenever `t ≤ t₀` and both scale factors are positive. -/
structure YRedSpecB (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Defining formula `y = 1 - a(t)/a(t₀)` (Cattoën–Visser; Bamba et al. §10). -/
  eq_one_sub : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → 0 < a t → 0 < a t₀ →
    Y a t₀ t = 1 - a t / a t₀
  /-- Same quantity as `y = z/(1+z)` with `z = a(t₀)/a(t) - 1` written out (the form quoted by
  Bamba et al. §10); a direct consequence of the first field, listed for fidelity to the source. -/
  eq_z_div : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → 0 < a t → 0 < a t₀ →
    Y a t₀ t = (a t₀ / a t - 1) / (1 + (a t₀ / a t - 1))

/-- Present total density parameter `Ω₀ = 8πGρ₀/(3H₀²)` from the Friedmann equation
`H² = 8πGρ/3 - K/a²` (Bamba et al. 2012 §10), hence `Ω₀ = 1 + K/(a₀² H₀²)` with `H₀ = ȧ(t₀)/a(t₀)`.
Determined for every `K` whenever `a t₀ ≠ 0`, `a` is differentiable at `t₀` and `ȧ(t₀) ≠ 0`
(`H₀ ≠ 0`; otherwise the density parameter has a zero denominator and is not constrained). -/
structure Omega0SpecB (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- `Ω₀ = 1 + K / (a(t₀)² H₀²)` with `H₀ = ȧ(t₀)/a(t₀)` written out; follows from the Friedmann
  equation with `Ω = 8πGρ/(3H²)`. -/
  eq_friedmann : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), a t₀ ≠ 0 → DifferentiableAt ℝ a t₀ →
    deriv a t₀ ≠ 0 →
    O K a t₀ = 1 + K / ((a t₀) ^ 2 * (deriv a t₀ / a t₀) ^ 2)

/-- Luminosity distance in a spatially flat FLRW model (`K = 0`), `d_L = a(t₀) (1+z) r` with comoving
coordinate distance `r = ∫_t^{t₀} ds / a(s)` (light travelling radially, `c = 1`) and
`1 + z = a(t₀)/a(t)` (Hogg 1999 §7; Weinberg §1.4; Bamba et al. 2012 §10). Determined whenever
`t ≤ t₀`, `a` is continuous on `[t, t₀]` and positive there. -/
structure LumDistFlatSpecB (D : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- `d_L = a(t₀) · (a(t₀)/a(t)) · ∫_t^{t₀} 1/a(s) ds`: positive continuous scale factor on the
  light's path, emission not after observation. -/
  eq_integral : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D a t₀ t = a t₀ * (a t₀ / a t) * ∫ s in t..t₀, 1 / a s

end Checked.Trust.SecondReadingSpecB
