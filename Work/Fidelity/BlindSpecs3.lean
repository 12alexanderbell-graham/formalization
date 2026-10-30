import Mathlib

/-!
# Blind specifications, batch 3: y-redshift, Ω₀, curvature parameter k, flat CPL Friedmann

Written from textbook cosmology only, independently of any implementation in this repository.

## Conventions
* Units with `c = 1`.
* `a : ℝ → ℝ` is the FLRW scale factor as a function of cosmic time.
* `t₀` is the observation ("present") time, `t` the emission time (`t < t₀` in the past).
* Redshift: `1 + z = a t₀ / a t`.
* Hubble rate: `H t = deriv a t / a t` (only meaningful when `a` is differentiable at `t`
  and `a t ≠ 0`; every law below that uses it carries these hypotheses explicitly).
* FLRW metric `ds² = -dt² + a(t)² [dχ² + S_K(χ)² dΩ²]` with a *real* curvature constant `K`
  (not normalised to `±1`). Under the rescaling `a ↦ c · a` (`c > 0`) the comoving radial
  coordinate rescales as `χ ↦ χ / c` and `K ↦ c² K`; the physical curvature `K / a²` is
  invariant, so the pair `(K, a)` is physically equivalent to `(c² K, c · a)`.
* Friedmann equation: `H² = (8πG/3) ρ − K / a²`; critical density `ρ_crit = 3 H² / (8πG)`.

References:
* [CV07] C. Cattoën and M. Visser, "The Hubble series: convergence properties and redshift
  variables", Class. Quantum Grav. 24 (2007) 5985, arXiv:gr-qc/0703122, §II (definition
  `y = z/(1+z)`), and eq. relating `y = 1 - a(t)/a(t₀)`.
* [Wei08] S. Weinberg, *Cosmology* (OUP 2008), §1.5 (Friedmann equation, `Ω_K`), §1.12.
* [Dod03] S. Dodelson, *Modern Cosmology* (2003), §2.4.
* [Pea99] J. A. Peacock, *Cosmological Physics* (1999), §3.2.
* [Ryd16] B. Ryden, *Introduction to Cosmology*, 2nd ed., §4.2–4.4 (Ω, curvature, de Sitter,
  Milne / empty universe).
* [CP01] M. Chevallier and D. Polarski, Int. J. Mod. Phys. D10 (2001) 213, gr-qc/0009008.
* [Lin03] E. V. Linder, Phys. Rev. Lett. 90 (2003) 091301, astro-ph/0208512.
-/

namespace Work.Fidelity.Blind3

open Filter Topology

/-! ## 1. The y-redshift of Cattoën & Visser -/

/-- Specification of the y-redshift `Y a t₀ t = z / (1 + z) = 1 − a(t)/a(t₀)` [CV07, §II].
It maps `z ∈ (−1, ∞)` bijectively onto `y ∈ (−∞, 1)`. Every field is only demanded on the
physical domain `a t₀ > 0`, `a t > 0`. -/
structure YRedSpec (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Determining law [CV07, §II: `y = z/(1+z) = 1 − a(t)/a(t₀)`]. -/
  law : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → Y a t₀ t = 1 - a t / a t₀
  /-- Definition through the ordinary redshift `z = a(t₀)/a(t) − 1` [CV07, §II]. -/
  of_z : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    Y a t₀ t = (a t₀ / a t - 1) / (1 + (a t₀ / a t - 1))
  /-- Inverse map `z = y / (1 − y)` [CV07, §II]. -/
  inv_z : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    a t₀ / a t - 1 = Y a t₀ t / (1 - Y a t₀ t)
  /-- Range: `y < 1` for every physical (positive) scale factor [CV07, §II]. -/
  lt_one : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → Y a t₀ t < 1
  /-- Sign: `y > 0` exactly for redshift (`a t < a t₀`), `y < 0` for blueshift. -/
  pos_iff : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → (0 < Y a t₀ t ↔ a t < a t₀)
  /-- Order preservation: `y` is strictly increasing in `z`, i.e. decreasing in `a t`. -/
  strictAnti_a : ∀ (a b : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t → 0 < b t →
    b t₀ = a t₀ → a t < b t → Y b t₀ t < Y a t₀ t
  /-- No redshift at the observation time. -/
  self : ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → Y a t₀ t₀ = 0
  /-- Anchor: de Sitter `a = exp(H t)` gives `y = 1 − exp(H (t − t₀))` [Ryd16, §5.3]. -/
  deSitter : ∀ (H t₀ t : ℝ), Y (fun s => Real.exp (H * s)) t₀ t = 1 - Real.exp (H * (t - t₀))
  /-- Anchor: Milne universe `a = t` gives `y = 1 − t/t₀` (for `t, t₀ > 0`) [Ryd16, §5.2]. -/
  milne : ∀ (t₀ t : ℝ), 0 < t₀ → 0 < t → Y (fun s => s) t₀ t = 1 - t / t₀
  /-- Anchor value: Milne, `t₀ = 2`, `t = 1`, so `z = 1` and `y = 1/2`. -/
  milne_value : Y (fun s => s) 2 1 = 1 / 2
  /-- Anchor: static universe `a ≡ c > 0` has no redshift. -/
  static : ∀ (c t₀ t : ℝ), 0 < c → Y (fun _ => c) t₀ t = 0
  /-- Invariance: `y` depends only on ratios of the scale factor, so it is unchanged by
  rescaling `a ↦ c · a` (`c > 0`), equivalently by the normalisation of `a`. -/
  scale_inv : ∀ (c : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), 0 < c → 0 < a t₀ → 0 < a t →
    Y (fun s => c * a s) t₀ t = Y a t₀ t
  /-- Invariance under time translation of the cosmic clock. -/
  shift_inv : ∀ (τ : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    Y (fun s => a (s + τ)) (t₀ - τ) (t - τ) = Y a t₀ t
  /-- Locality: `y` depends only on the two values `a t₀`, `a t`. -/
  local_values : ∀ (a b : ℝ → ℝ) (t₀ t : ℝ), 0 < a t₀ → 0 < a t →
    a t₀ = b t₀ → a t = b t → Y a t₀ t = Y b t₀ t
  /-- Near miss: `y ≠ z / (1 − z)` (Milne, `t₀ = 3`, `t = 1`: `z = 2`, `z/(1−z) = −2`,
  but `y = 2/3`). -/
  not_z_div_one_sub_z : Y (fun s => s) 3 1 ≠ -2
  /-- Near miss: `y ≠ z` (Milne, `t₀ = 2`, `t = 1`: `z = 1`, `y = 1/2`). -/
  not_z : Y (fun s => s) 2 1 ≠ 1
  /-- Near miss (sign flip): `y ≠ a(t)/a(t₀) − 1` (that would give `−1/2` here). -/
  not_neg : Y (fun s => s) 2 1 ≠ -1 / 2
  /-- Near miss: `y ≠ 1 − a(t₀)/a(t) = −z` (that would give `−1` here). -/
  not_neg_z : Y (fun s => s) 2 1 ≠ -1
  /-- Near miss: `y ≠ log(1 + z)` (that would give `log 2` here). -/
  not_log : Y (fun s => s) 2 1 ≠ Real.log 2

/-! ## 2. Present-day total density parameter Ω₀ -/

/-- Specification of `O K a t₀ = Ω₀ = ρ_total(t₀) / ρ_crit(t₀)` for an FLRW model with curvature
constant `K`. From the Friedmann equation `H² = (8πG/3)ρ − K/a²` and `ρ_crit = 3H²/(8πG)`:
`Ω₀ = 1 + K / (a₀ H₀)² = 1 + K / ȧ(t₀)²` [Wei08, eq. (1.5.19)–(1.5.21); Ryd16, eq. (4.34)].
All fields demand values only when `a t₀ > 0`, `a` is differentiable at `t₀`, and `H₀ ≠ 0`. -/
structure Omega0Spec (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Determining law: `Ω₀ = 1 + K/(a₀ H₀)²` [Ryd16, eq. (4.34): `1 − Ω₀ = −K/(a₀H₀)²`]. -/
  law : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 →
    O K a t₀ = 1 + K / (a t₀ ^ 2 * (deriv a t₀ / a t₀) ^ 2)
  /-- Defining law via the Friedmann equation: if the total density `ρ` satisfies
  `H₀² = (8πG/3)ρ − K/a₀²` (for some `G > 0`), then `Ω₀ = ρ / ρ_crit = (8πG/3)ρ / H₀²`
  [Wei08, §1.5; Dod03, §2.4]. -/
  friedmann : ∀ (G ρ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < G → 0 < a t₀ →
    DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 →
    (deriv a t₀ / a t₀) ^ 2 = 8 * Real.pi * G / 3 * ρ - K / a t₀ ^ 2 →
    O K a t₀ = ρ / (3 * (deriv a t₀ / a t₀) ^ 2 / (8 * Real.pi * G))
  /-- Anchor: spatially flat (`K = 0`) ⇒ `Ω₀ = 1` [Ryd16, §4.4]. -/
  flat : ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → O 0 a t₀ = 1
  /-- Anchor: Milne (empty) universe `a = t`, `K = −1` ⇒ `Ω₀ = 0` [Ryd16, §5.2]. -/
  milne : ∀ t₀ : ℝ, 0 < t₀ → O (-1) (fun s => s) t₀ = 0
  /-- Anchor: closed de Sitter slicing `a = cosh t`, `K = 1` (`H² = 1 − 1/a²`, i.e. a pure
  cosmological constant with `(8πG/3)ρ_Λ = 1`) ⇒ `Ω₀ = 1/H₀² = 1 + 1/sinh² t₀`. -/
  closed_deSitter : ∀ t₀ : ℝ, t₀ ≠ 0 →
    O 1 Real.cosh t₀ = 1 + 1 / Real.sinh t₀ ^ 2
  /-- Anchor: closed model with `a = t`, `K = 1` (so `ȧ = 1`) ⇒ `Ω₀ = 2`. -/
  closed_value : O 1 (fun s => s) 1 = 2
  /-- Closed (`K > 0`) ⇔ `Ω₀ > 1` [Ryd16, §4.4]. -/
  gt_one_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (1 < O K a t₀ ↔ 0 < K)
  /-- Open (`K < 0`) ⇔ `Ω₀ < 1` [Ryd16, §4.4]. -/
  lt_one_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (O K a t₀ < 1 ↔ K < 0)
  /-- Rescaling law: `(K, a) ↦ (c² K, c · a)` describes the same spacetime, so `Ω₀` is
  unchanged (`c > 0`). -/
  rescale : ∀ (c K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < c → 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → O (c ^ 2 * K) (fun s => c * a s) t₀ = O K a t₀
  /-- Invariance under time translation. -/
  shift_inv : ∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → O K (fun s => a (s + τ)) (t₀ - τ) = O K a t₀
  /-- Locality: depends only on the germ of `a` at `t₀`. -/
  local_germ : ∀ (K : ℝ) (a b : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → a =ᶠ[𝓝 t₀] b → O K a t₀ = O K b t₀
  /-- Near miss (sign): `Ω₀ ≠ 1 − K/(a₀H₀)²` (closed `a = t`, `K = 1`, `t₀ = 1` would give 0). -/
  not_sign_flip : O 1 (fun s => s) 1 ≠ 0
  /-- Near miss: `Ω₀ ≠ 1 + K/H₀²` (missing `a₀²`): `a = 2t`, `K = 1`, `t₀ = 1` has
  `H₀ = 1`, `a₀ = 2`, so `Ω₀ = 5/4`, not `2`. -/
  not_missing_a0 : O 1 (fun s => 2 * s) 1 ≠ 2

/-! ## 3. Dimensionless curvature parameter k = K/(H₀a₀)², Ω_k = −k -/

/-- Specification of `k K a t₀ = K / (H₀ a₀)²` (with `c = 1`), the dimensionless curvature
parameter, so that the curvature density parameter is `Ω_k = −k` and `Ω₀ = 1 − Ω_k = 1 + k`
[Wei08, eq. (1.5.21) `Ω_K = −K/(a₀H₀)²`; Dod03, §2.4]. -/
structure CurvKSpec (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Determining law `k = K / (H₀ a₀)²`. -/
  law : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 →
    k K a t₀ = K / ((deriv a t₀ / a t₀) * a t₀) ^ 2
  /-- Equivalent form: `k = K / ȧ(t₀)²`. -/
  law_adot : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ ≠ 0 → k K a t₀ = K / deriv a t₀ ^ 2
  /-- Closure relation `Ω₀ = 1 − Ω_k = 1 + k`: if the total density obeys the Friedmann
  equation `H₀² = (8πG/3)ρ − K/a₀²`, then `(8πG/3)ρ/H₀² = 1 + k` [Wei08, eq. (1.5.20)]. -/
  friedmann : ∀ (G ρ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < G → 0 < a t₀ →
    DifferentiableAt ℝ a t₀ → deriv a t₀ / a t₀ ≠ 0 →
    (deriv a t₀ / a t₀) ^ 2 = 8 * Real.pi * G / 3 * ρ - K / a t₀ ^ 2 →
    8 * Real.pi * G / 3 * ρ / (deriv a t₀ / a t₀) ^ 2 = 1 + k K a t₀
  /-- Anchor: flat ⇒ `k = 0`. -/
  flat : ∀ (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k 0 a t₀ = 0
  /-- Anchor: Milne `a = t`, `K = −1` ⇒ `k = −1` (`Ω_k = 1`). -/
  milne : ∀ t₀ : ℝ, 0 < t₀ → k (-1) (fun s => s) t₀ = -1
  /-- Anchor: closed de Sitter `a = cosh t`, `K = 1` ⇒ `k = 1 / sinh² t₀`. -/
  closed_deSitter : ∀ t₀ : ℝ, t₀ ≠ 0 → k 1 Real.cosh t₀ = 1 / Real.sinh t₀ ^ 2
  /-- Sign: `k` has the sign of `K` (closed `k > 0`, open `k < 0`). -/
  pos_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (0 < k K a t₀ ↔ 0 < K)
  neg_iff : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → (k K a t₀ < 0 ↔ K < 0)
  /-- Linearity in `K` at fixed expansion history. -/
  linear_K : ∀ (r K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k (r * K) a t₀ = r * k K a t₀
  /-- Rescaling invariance: `(K, a) ↦ (c² K, c · a)` leaves `k` unchanged (`c > 0`). -/
  rescale : ∀ (c K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < c → 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k (c ^ 2 * K) (fun s => c * a s) t₀ = k K a t₀
  /-- Invariance under time translation. -/
  shift_inv : ∀ (τ K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), 0 < a t₀ → DifferentiableAt ℝ a t₀ →
    deriv a t₀ / a t₀ ≠ 0 → k K (fun s => a (s + τ)) (t₀ - τ) = k K a t₀
  /-- Near miss (sign): `k ≠ Ω_k = −K/(H₀a₀)²` (Milne would give `+1`). -/
  not_omega_k : k (-1) (fun s => s) 1 ≠ 1
  /-- Near miss: `k ≠ K/H₀²` (missing `a₀`): `a = 2t`, `K = −4`, `t₀ = 1` has `k = −1`,
  while `K/H₀² = −4`. -/
  not_missing_a0 : k (-4) (fun s => 2 * s) 1 ≠ -4
  /-- Anchor value for the preceding near miss. -/
  value_2t : k (-4) (fun s => 2 * s) 1 = -1

/-! ## 4. Flat Friedmann with matter + CPL dark energy -/

/-- `FriedmannCPL Ω w₀ wₐ a t₀`: near `t₀`, `a` solves the flat Friedmann equation
(units `8πG/3 = 1`) `H² = ρ_m + ρ_de` with
* pressureless matter, `ρ_m a³ = const` [Ryd16, eq. (5.7)];
* a dark-energy fluid with CPL equation of state `w(z) = w₀ + wₐ z/(1+z)`, `z` measured from
  `t₀` [CP01; Lin03, eq. (3)]; since `z/(1+z) = 1 − a(t)/a(t₀)` this is
  `w = w₀ + wₐ (1 − a(t)/a(t₀))`, i.e. `w(a) = w₀ + wₐ(1 − a/a₀)`;
  separately conserved: `ρ̇_de + 3H(1 + w)ρ_de = 0` [Wei08, eq. (1.5.18)];
* the universe expanding at `t₀` (`ȧ(t₀) > 0`);
* `Ω = ρ_m(t₀) / ρ_crit(t₀) = ρ_m(t₀) / H₀²` (with `8πG/3 = 1`, `ρ_crit = H²`).

No sign is imposed on `Ω`, `w₀`, `wₐ` or the densities. Junk values are excluded: `a > 0`
and differentiable on a neighbourhood (so `deriv a` is the true derivative and `H` has no
zero denominator), and the expansion condition makes `H₀ > 0` so `Ω`'s defining quotient
is well-posed. -/
def FriedmannCPL (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ∃ ρm ρde : ℝ → ℝ,
    (∀ᶠ t in 𝓝 t₀,
      0 < a t ∧
      DifferentiableAt ℝ a t ∧
      -- flat Friedmann equation, 8πG/3 = 1
      (deriv a t / a t) ^ 2 = ρm t + ρde t ∧
      -- pressureless matter: ρ_m a³ conserved
      ρm t * a t ^ 3 = ρm t₀ * a t₀ ^ 3 ∧
      -- dark-energy continuity equation with CPL w(t) = w₀ + wₐ z/(1+z), z/(1+z) = 1 − a/a₀
      HasDerivAt ρde
        (-(3 * (deriv a t / a t) * (1 + (w₀ + wₐ * (1 - a t / a t₀))) * ρde t)) t) ∧
    -- expanding at t₀
    0 < deriv a t₀ ∧
    -- present matter density parameter
    Ω = ρm t₀ / (deriv a t₀ / a t₀) ^ 2

end Work.Fidelity.Blind3
