import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Blind specifications of seven cosmography quantities (reading A)

Units `c = 1`; `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic time, `t₀` the time of
observation, `t` the time of emission, `K` the curvature constant of
`ds² = −dt² + a(t)² (dr²/(1 − K r²) + r² dΩ²)`.
In every structure the scale factor is assumed positive at the points where the quantity is
meaningful; nothing is said about points where the source's quantity is undefined.
-/

namespace Checked.Trust.SecondReadingSpecA

/-- Hubble expansion rate `H = ȧ/a` (Weinberg, *Cosmology*, §1.5; Hogg 1999, astro-ph/9905116, §3).
The specification determines `H a t` whenever `a t > 0` and `a` is differentiable at `t`.
It says nothing where `a t ≤ 0` or where `a` is not differentiable at `t`. -/
structure HubbleSpecA (H : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Defining formula `H = (da/dt)/a` (Weinberg §1.5; Hogg §3), for positive scale factor and
  `a` differentiable at `t`. -/
  def_formula : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t →
    H a t = deriv a t / a t

/-- Deceleration parameter `q = −ä a / ȧ² = −ä/(a H²)` (Weinberg §1.5; Visser 2004,
gr-qc/0309109). The specification determines `Q a t` whenever `a t > 0`, `a` is twice
differentiable at `t` (meaning `a` and `deriv a` are differentiable at `t`) and `ȧ(t) ≠ 0`. Nothing is said where `ȧ(t) = 0` (Hubble rate zero, `q`
undefined) or where `a t ≤ 0`. -/
structure DecelSpecA (Q : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Defining formula `q = −(1/(a H²)) d²a/dt² = −a ä / ȧ²` with `H = ȧ/a` spelled out
  (Weinberg §1.5; Visser 2004). Hypotheses: `a t > 0`, `a` and `deriv a` differentiable at `t`,
  `ȧ(t) ≠ 0`. -/
  def_formula : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → DifferentiableAt ℝ a t →
    DifferentiableAt ℝ (deriv a) t → deriv a t ≠ 0 →
    Q a t = - (iteratedDeriv 2 a t) / (a t * (deriv a t / a t) ^ 2)

/-- Cosmological redshift `z` of light emitted at `t` and observed at `t₀`, defined by
`1 + z = a(t₀)/a(t)` (Weinberg §1.2; Hogg 1999 §2). The specification determines `Z a t₀ t`
whenever `a t > 0` and `a t₀ > 0` (no ordering of `t`, `t₀` is imposed). Nothing is said when
either scale factor is `≤ 0`. -/
structure RedshiftSpecA (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Defining relation `1 + z = a(t₀)/a(t)`, i.e. `z = a(t₀)/a(t) − 1` (Weinberg §1.2; Hogg §2). -/
  def_formula : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t → 0 < a t₀ →
    Z a t₀ t = a t₀ / a t - 1

/-- Cosmographic coefficients of Aviles, Gruber, Luongo, Quevedo 2012 (arXiv:1204.2007, Eq. (3)):
`H = ȧ/a`, `q = −a''/(a H²)`, `j = a'''/(a H³)`, `s = a''''/(a H⁴)`, `l = a⁽⁵⁾/(a H⁵)`; the
pattern for `n ≥ 3` is `C n = a⁽ⁿ⁾/(a Hⁿ)` (jerk, snap, lerk at `n = 3, 4, 5`, and `n = 6`
following the pattern, which is my extrapolation of the displayed pattern), and `n = 2` is the
deceleration parameter with a minus sign. The specification determines `C n a t` for all `n ≥ 2`
whenever `a t > 0`, `ȧ(t) ≠ 0` (so `H ≠ 0`) and `a` is `n` times continuously differentiable
at `t`. It says nothing for `n = 0, 1` (the source's list starts with `H` and `q`; `n = 1` would
be `H` itself, which does not fit the pattern `a⁽ⁿ⁾/(aHⁿ)`) and nothing where `H = 0`. -/
structure CoeffSpecA (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- `n = 2`: `q = −(1/(a H²)) d²a/dt²` with `H = ȧ/a` spelled out (Eq. (3) of the source). -/
  decel : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → deriv a t ≠ 0 → ContDiffAt ℝ 2 a t →
    C 2 a t = - (iteratedDeriv 2 a t) / (a t * (deriv a t / a t) ^ 2)
  /-- `n ≥ 3`: `C n = (1/(a H^n)) dⁿa/dtⁿ` with `H = ȧ/a` spelled out (jerk, snap, lerk are
  `n = 3, 4, 5`; Eq. (3) of the source; the extension to all `n ≥ 3` is the pattern). -/
  pattern : ∀ (n : ℕ), 3 ≤ n → ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → deriv a t ≠ 0 →
    ContDiffAt ℝ (n : ℕ) a t →
    C n a t = iteratedDeriv n a t / (a t * (deriv a t / a t) ^ n)

/-- The y-redshift of Cattoën and Visser 2007 (gr-qc/0703122), used in Bamba, Capozziello,
Nojiri, Odintsov 2012 (arXiv:1205.3421, §10): `y = z/(1+z) = 1 − a(t)/a(t₀)`, with `z` the
redshift `1 + z = a(t₀)/a(t)`. The specification determines `Y a t₀ t` whenever `a t > 0` and
`a t₀ > 0`; nothing otherwise. -/
structure YRedSpecA (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Defining formula `y = z/(1+z)` with `z = a(t₀)/a(t) − 1` spelled out (Cattoën–Visser 2007;
  Bamba et al. §10). Equivalent to `y = 1 − a(t)/a(t₀)`. -/
  def_formula : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t → 0 < a t₀ →
    Y a t₀ t = (a t₀ / a t - 1) / (1 + (a t₀ / a t - 1))

/-- Present total density parameter `Ω₀ = ρ₀/ρ_crit` of an FLRW model with curvature constant `K`.
The Friedmann equation `H² + K/a² = (8πG/3) ρ` gives, with `ρ_crit = 3H²/(8πG)`,
`Ω₀ = 1 + K/(a₀² H₀²)` (Bamba et al. 2012 §10; Weinberg §1.5). The specification determines
`O K a t₀` whenever `a t₀ > 0`, `a` is differentiable at `t₀` and `ȧ(t₀) ≠ 0` (`H₀ ≠ 0`);
nothing where `H₀ = 0` or `a t₀ ≤ 0`. -/
structure Omega0SpecA (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- `Ω₀ = 1 + K/(a(t₀)² H₀²)` with `H₀ = ȧ(t₀)/a(t₀)` spelled out; this is the Friedmann
  equation rewritten as `Ω₀ − 1 = K/(a₀H₀)²`. -/
  def_formula : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ ≠ 0 →
    O K a t₀ = 1 + K / ((a t₀) ^ 2 * (deriv a t₀ / a t₀) ^ 2)

/-- Luminosity distance in a spatially flat FLRW model (`K = 0`), for light emitted at `t ≤ t₀`
and received at `t₀`: `d_L = (1+z) a(t₀) r` where `r = ∫_t^{t₀} ds/a(s)` is the comoving
(coordinate) distance for `c = 1` and `1 + z = a(t₀)/a(t)` (Hogg 1999 §7, `d_L = (1+z) d_M` with
`d_M = d_C` for a flat universe; Weinberg §1.4; Bamba et al. §10). The specification determines
`D a t₀ t` whenever `t ≤ t₀`, `a` is continuous and positive on `[t, t₀]`; nothing otherwise. -/
structure LumDistFlatSpecA (D : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- `d_L = (a(t₀)/a(t)) · a(t₀) · ∫_t^{t₀} ds / a(s)` (flat model, `c = 1`), for `a` continuous
  and positive on `[t, t₀]`. -/
  def_formula : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D a t₀ t = (a t₀ / a t) * a t₀ * ∫ s in t..t₀, 1 / a s

end Checked.Trust.SecondReadingSpecA
