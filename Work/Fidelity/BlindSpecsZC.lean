import Mathlib

/-!
# Blind specifications: cosmological redshift `Z` and cosmographic coefficients `C`

Written blind (without reading the definitions under test), from textbook cosmology.

## Conventions
* Units with `c = 1`.
* `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic time.
* The Hubble rate is `H(t) = ȧ/a`, written `deriv a t / a t`.
* `t₀` is the observation time, `t` the emission time; `t < t₀` is the past.
* `Z a t₀ t` is the redshift `z` of light emitted at `t` and received at `t₀`.
* `C n a t = a⁽ⁿ⁾(t) / (a(t) · H(t)ⁿ)`, the dimensionless cosmographic coefficients:
  `C 0 = 1`, `C 1 = 1`, `C 2 = -q` (deceleration), `C 3 = j` (jerk), `C 4 = s` (snap),
  `C 5 = l` (lerk), `C 6 = m`.

## Physical domain
* `Z` is only constrained where `a > 0` and `a` is `C¹` on the closed interval between the
  emission and observation times (the light ray's time span).
* `C n a t` is only constrained where `a t > 0`, `a` is `C^n` near `t` (`ContDiffAt ℝ n a t`,
  which for finite `n` means `C^n` on a neighbourhood) and `ȧ(t) ≠ 0` (so that `H ≠ 0`).

## Sources
* [Weinberg] S. Weinberg, *Cosmology* (OUP 2008), §1.2 (redshift, Hubble law expansion).
* [Ryden] B. Ryden, *Introduction to Cosmology* (2nd ed.), §3.5 (eq. 3.46 `1+z = a(t₀)/a(t)`).
* [Peebles] P.J.E. Peebles, *Principles of Physical Cosmology*, §5 (wavelength stretching).
* [Visser] M. Visser, "Jerk, snap and the cosmological equation of state",
  Class. Quant. Grav. 21 (2004) 2603, gr-qc/0309109, eqs. (1)–(7).
* [Aviles] A. Aviles, C. Gruber, O. Luongo, H. Quevedo, "Cosmography and constraints on the
  equation of state of the Universe in various parametrizations", PRD 86 (2012) 123516,
  §II (definitions of `q, j, s, l, m`).
-/

namespace Work.Fidelity.BlindZC

open Set Filter Asymptotics intervalIntegral

/-- Physical hypotheses for a light ray between times `t` and `t₀`: the scale factor is
positive and continuously differentiable on the closed interval between them. -/
def RayOK (a : ℝ → ℝ) (t t₀ : ℝ) : Prop :=
  (∀ s ∈ uIcc t t₀, 0 < a s) ∧ ContDiffOn ℝ 1 a (uIcc t t₀)

/-- Specification of the cosmological redshift `Z a t₀ t`. -/
structure RedshiftSpec (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- **General (pinning) law: integrated wavelength stretching.** Along a radial null ray
  `dλ/λ = (ȧ/a) dt`, hence `1 + z = λ_obs/λ_em = exp ∫_t^{t₀} H(s) ds`.
  [Peebles §5; Weinberg §1.2; Ryden §3.5]. -/
  integral_law : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ →
    1 + Z a t₀ t = Real.exp (∫ s in t..t₀, deriv a s / a s)
  /-- **Ratio law** `1 + z = a(t₀)/a(t)` [Ryden eq. 3.46; Weinberg eq. 1.2.4]. -/
  ratio_law : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ →
    1 + Z a t₀ t = a t₀ / a t
  /-- No redshift when emission and observation coincide. -/
  self_zero : ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t → Z a t t = 0
  /-- **Composition**: redshift factors multiply along a ray passing an intermediate
  observer at `t₁` [Weinberg §1.2]. -/
  compose : ∀ (a : ℝ → ℝ) (t t₁ t₀ : ℝ), RayOK a t t₁ → RayOK a t₁ t₀ →
    1 + Z a t₀ t = (1 + Z a t₀ t₁) * (1 + Z a t₁ t)
  /-- **Normalization invariance**: only ratios of the scale factor are physical, so
  `a ↦ c·a` (`c > 0`) leaves `z` unchanged [Ryden §3.5]. -/
  rescale_invariant : ∀ (a : ℝ → ℝ) (c t₀ t : ℝ), 0 < c → RayOK a t t₀ →
    Z (fun s => c * a s) t₀ t = Z a t₀ t
  /-- **Time-translation covariance** (choice of time origin is unphysical). -/
  time_translate : ∀ (a : ℝ → ℝ) (τ t₀ t : ℝ), RayOK a (t + τ) (t₀ + τ) →
    Z (fun s => a (s + τ)) t₀ t = Z a (t₀ + τ) (t + τ)
  /-- **Locality**: `z` depends only on the scale factor along the ray. -/
  local_dep : ∀ (a b : ℝ → ℝ) (t₀ t : ℝ), RayOK a t t₀ → EqOn a b (uIcc t t₀) →
    Z b t₀ t = Z a t₀ t
  /-- **Expanding universe ⇒ redshift** (`z > 0` for past emission when `ȧ > 0`). -/
  expanding_pos : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t < t₀ → RayOK a t t₀ →
    (∀ s ∈ Ioo t t₀, 0 < deriv a s) → 0 < Z a t₀ t
  /-- Emission-time derivative: `∂z/∂t_em = -(1+z) H(t_em)`. -/
  deriv_emission : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), (∀ s, 0 < a s) → ContDiff ℝ 1 a →
    HasDerivAt (fun s => Z a t₀ s) (-(1 + Z a t₀ t) * (deriv a t / a t)) t
  /-- Observation-time derivative (redshift drift kernel): `∂(1+z)/∂t₀ = (1+z) H(t₀)`. -/
  deriv_observation : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), (∀ s, 0 < a s) → ContDiff ℝ 1 a →
    HasDerivAt (fun s => Z a s t) ((1 + Z a t₀ t) * (deriv a t₀ / a t₀)) t₀
  /-- **Low-redshift (Hubble-law) expansion to second order** in the look-back time
  `Δ = t₀ - t`: `z = H₀Δ + (1 + q₀/2) H₀² Δ² + o(Δ²)`, with `(1 + q₀/2)H₀² = H₀² - ä₀/(2a₀)`
  [Weinberg eq. 1.4.x; Visser eq. (12)]. -/
  low_z : ∀ (a : ℝ → ℝ) (t₀ : ℝ), (∀ s, 0 < a s) → ContDiff ℝ 2 a →
    (fun Δ : ℝ => Z a t₀ (t₀ - Δ) -
        ((deriv a t₀ / a t₀) * Δ +
          ((deriv a t₀ / a t₀) ^ 2 - iteratedDeriv 2 a t₀ / (2 * a t₀)) * Δ ^ 2))
      =o[nhds 0] (fun Δ : ℝ => Δ ^ 2)
  /-- **Anchor: de Sitter** `a = A e^{ht}`: `1 + z = e^{h(t₀-t)}`. -/
  de_sitter : ∀ (A h t₀ t : ℝ), 0 < A →
    Z (fun s => A * Real.exp (h * s)) t₀ t = Real.exp (h * (t₀ - t)) - 1
  /-- **Anchor: power law** `a = t^p` (e.g. matter `p = 2/3`, radiation `p = 1/2`),
  for positive times: `1 + z = (t₀/t)^p`. -/
  power_law : ∀ (p t₀ t : ℝ), 0 < t → 0 < t₀ →
    Z (fun s => s ^ p) t₀ t = t₀ ^ p / t ^ p - 1
  /-- **Anchor: Milne** `a = t`: `1 + z = t₀/t`. -/
  milne : ∀ (t₀ t : ℝ), 0 < t → 0 < t₀ → Z (fun s => s) t₀ t = t₀ / t - 1
  /-- **Anchor: static universe** `a = A`: no cosmological redshift. -/
  static : ∀ (A t₀ t : ℝ), 0 < A → Z (fun _ => A) t₀ t = 0
  /-- **Near-miss negative**: the linear Hubble law `z = H₀(t₀ - t)` is not exact
  (de Sitter, `h = 1`, `t₀ - t = 1`: true `z = e - 1`, not `1`). -/
  not_linear_hubble : Z (fun s => Real.exp s) 1 0 ≠ 1
  /-- **Near-miss negative**: the ratio is not inverted (`z ≠ a(t)/a(t₀) - 1`). -/
  not_inverted : Z (fun s => Real.exp s) 1 0 ≠ Real.exp (-1) - 1

/-- Physical hypotheses for the `n`-th cosmographic coefficient at `t`. -/
def CoeffOK (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : Prop :=
  0 < a t ∧ ContDiffAt ℝ n a t ∧ deriv a t ≠ 0

/-- Specification of the dimensionless cosmographic coefficients `C n a t`. -/
structure CosmoCoeffSpec (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- **Defining formula** `C n = a⁽ⁿ⁾ / (a Hⁿ)`, `H = ȧ/a`
  [Visser eqs. (1)–(5); Aviles et al. §II]. -/
  defining : ∀ (n : ℕ) (a : ℝ → ℝ) (t : ℝ), CoeffOK n a t →
    C n a t = iteratedDeriv n a t / (a t * (deriv a t / a t) ^ n)
  /-- **General (pinning) law: cosmographic Taylor series** of the scale factor,
  `a(t₀+Δ)/a(t₀) = Σ_{k=0}^{n} C k · (H₀Δ)^k / k! + o(Δⁿ)`, valid when `a` is `C^n` near
  `t₀` (Peano remainder) [Visser eq. (6); Aviles et al. eq. (2)]. -/
  taylor_law : ∀ (n : ℕ) (a : ℝ → ℝ) (t₀ : ℝ), CoeffOK n a t₀ →
    (fun Δ : ℝ => a (t₀ + Δ) / a t₀ -
        ∑ k ∈ Finset.range (n + 1),
          C k a t₀ * (deriv a t₀ / a t₀ * Δ) ^ k / (k.factorial : ℝ))
      =o[nhds 0] (fun Δ : ℝ => Δ ^ n)
  /-- `C 0 = 1` (normalization by `a`). -/
  zero : ∀ (a : ℝ → ℝ) (t : ℝ), CoeffOK 0 a t → C 0 a t = 1
  /-- `C 1 = ȧ/(aH) = 1`. -/
  one : ∀ (a : ℝ → ℝ) (t : ℝ), CoeffOK 1 a t → C 1 a t = 1
  /-- **Deceleration via the Hubble rate**: `-q = 1 + Ḣ/H²` [Visser eq. (7)]. -/
  decel_hubble : ∀ (a : ℝ → ℝ) (t : ℝ), CoeffOK 2 a t →
    C 2 a t = 1 + deriv (fun s => deriv a s / a s) t / (deriv a t / a t) ^ 2
  /-- **Recursion (time evolution)**: with `Ḣ/H² = C₂ - 1`,
  `dCₙ/dt = H (C_{n+1} - Cₙ (1 + n (C₂ - 1)))`; for `n = 2` this is Visser's
  `q̇ = H(q + 2q² - j)` [Visser eq. (8)ff; Aviles et al. §II]. -/
  recursion : ∀ (n : ℕ) (a : ℝ → ℝ) (t : ℝ), CoeffOK (n + 1) a t →
    HasDerivAt (fun s => C n a s)
      ((deriv a t / a t) * (C (n + 1) a t - C n a t * (1 + (n : ℝ) * (C 2 a t - 1)))) t
  /-- **Normalization invariance**: `a ↦ c·a` (`c > 0`) leaves every `C n` unchanged. -/
  rescale_invariant : ∀ (n : ℕ) (a : ℝ → ℝ) (c t : ℝ), 0 < c → CoeffOK n a t →
    C n (fun s => c * a s) t = C n a t
  /-- **Time-translation covariance**. -/
  time_translate : ∀ (n : ℕ) (a : ℝ → ℝ) (τ t : ℝ), CoeffOK n a (t + τ) →
    C n (fun s => a (s + τ)) t = C n a (t + τ)
  /-- **Time-unit (and time-reversal) invariance**: the coefficients are dimensionless, so
  `a(t) ↦ a(λt)`, `λ ≠ 0`, leaves them unchanged (`λ = -1`: both `a⁽ⁿ⁾` and `Hⁿ` pick
  up `(-1)ⁿ`). -/
  time_scale : ∀ (n : ℕ) (a : ℝ → ℝ) (lam t : ℝ), lam ≠ 0 → CoeffOK n a (lam * t) →
    C n (fun s => a (lam * s)) t = C n a (lam * t)
  /-- **Anchor: de Sitter** `a = A e^{ht}`, `h ≠ 0`: `q = -1`, `j = s = … = 1`,
  i.e. `C n = 1` for all `n` [Visser §3]. -/
  de_sitter : ∀ (n : ℕ) (A h t : ℝ), 0 < A → h ≠ 0 →
    C n (fun s => A * Real.exp (h * s)) t = 1
  /-- **Anchor: power law** `a = t^p`, `t > 0`, `p ≠ 0`:
  `C n = p(p-1)⋯(p-n+1)/pⁿ` (matter `p = 2/3`: `q = 1/2`, `j = 1`;
  radiation `p = 1/2`: `q = 1`). -/
  power_law : ∀ (n : ℕ) (p t : ℝ), 0 < t → p ≠ 0 →
    C n (fun s => s ^ p) t = (∏ i ∈ Finset.range n, (p - (i : ℝ))) / p ^ n
  /-- **Anchor: Milne** `a = t`: coasting, `q = j = s = … = 0` (`C n = 0` for `n ≥ 2`). -/
  milne : ∀ (n : ℕ) (t : ℝ), 0 < t → 2 ≤ n → C n (fun s => s) t = 0
  /-- **Anchor: matter domination** `a ∝ t^{2/3}`: deceleration `q = 1/2`, jerk `j = 1`. -/
  matter_q : ∀ (t : ℝ), 0 < t → C 2 (fun s => s ^ (2 / 3 : ℝ)) t = -1 / 2
  matter_j : ∀ (t : ℝ), 0 < t → C 3 (fun s => s ^ (2 / 3 : ℝ)) t = 1
  /-- **Near-miss negative (sign)**: `C 2` is `-q`, not `q` (matter: `q = 1/2`). -/
  not_q_sign : C 2 (fun s => s ^ (2 / 3 : ℝ)) 1 ≠ 1 / 2
  /-- **Near-miss negative (normalization)**: `C 2` is not the unnormalized `ä/a`
  (de Sitter `h = 2`: `ä/a = 4`, but `C 2 = 1`). -/
  not_unnormalized : C 2 (fun s => Real.exp (2 * s)) 0 ≠ 4

end Work.Fidelity.BlindZC
