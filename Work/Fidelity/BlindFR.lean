import Mathlib

/-!
# Blind specification: metric F(R) gravity + dust in flat FLRW

Independent ("blind") specification of the flat-FLRW cosmological equations of metric
F(R) gravity sourced by pressureless matter, written without consulting the definitions
under test.

## Sources
* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, Rev. Mod. Phys. 82, 451 (2010), §IV.
* A. De Felice, S. Tsujikawa, *f(R) theories*, Living Rev. Rel. 13, 3 (2010), §2–3
  (eqs. (2.15)–(2.16) there).
* S. Capozziello, V. F. Cardone, V. Salzano, *Cosmography of f(R) gravity*,
  PRD 78, 063504 (2008).
* K. Bamba, S. Capozziello, S. Nojiri, S. D. Odintsov, arXiv:1205.3421, §XI
  (the source being formalized; it fixes the sign convention below).

## Units
`c = 1`, `κ² = 8πG = 1`.

## Sign convention (IMPORTANT)
We use the convention in which the Ricci scalar of de Sitter space with `H > 0` is
**negative**:  `R = −6 (Ḣ + 2H²) = −6 (ä/a + ȧ²/a²)`, so de Sitter has `R = −12 H²`.

Relation to the more common convention (signature `(−,+,+,+)`, MTW curvature
conventions, de Sitter `R_c = +12 H²`), where the action is
`S = ∫ √−g [ f(R_c)/(2κ²) ] + S_m`:

* `R = −R_c`  (and `R_μν = −R^c_μν`, `ä`, `ȧ`, `a` unchanged);
* `F(R) = − f(−R)`, i.e. `f(R_c) = −F(−R_c)`.

With this map the *first* derivative is unchanged as a function of time,
`F′(R) = f′(R_c)` (so the effective gravitational coupling `F′ > 0` keeps its sign), while
`F″(R) = − f″(R_c)`, `F‴(R) = f‴(R_c)`.  Consequently
`d F′/dt = F″ Ṙ = f″ Ṙ_c` and `d²F′/dt² = F‴ Ṙ² + F″ R̈ = f‴ Ṙ_c² + f″ R̈_c`
are convention independent.  GR is `f(R_c) = R_c` ↦ `F(R) = R` (same form in both
conventions), and ΛCDM, `f(R_c) = R_c − 2Λ`, becomes **`F(R) = R + 2Λ`** in this convention
(the constant flips sign because `F(R) = −f(−R)`).

## Derivation (common convention first)
Field equations (metric formalism):
`f′ R^c_μν − ½ f g_μν − ∇_μ∇_ν f′ + g_μν □ f′ = κ² T_μν`.
Flat FLRW `ds² = −dt² + a² dx²`, `H = ȧ/a`, perfect fluid `T_00 = ρ`, `T_ij = p a² δ_ij`.
Write `φ(t) = f′(R_c(t))`. Then
* `R^c_00 = −3 ä/a = −3(Ḣ + H²)`, `R^c_ij = (a ä + 2ȧ²) δ_ij`,
  `R_c = 6(Ḣ + 2H²)`;
* `∇_0∇_0 φ = φ̈`, `∇_i∇_j φ = −Γ^0_ij φ̇ = −a ȧ φ̇ δ_ij`,
  `□φ = −φ̈ − 3Hφ̇`.
00 component: `−3(Ḣ+H²)φ + ½ f − φ̈ − (−φ̈ − 3Hφ̇) = κ²ρ`; using
`Ḣ + H² = R_c/6 − H²` this is
`3 φ H² = κ²ρ + ½(φ R_c − f) − 3 H φ̇`                                   (C)
(De Felice–Tsujikawa (2.15)).  ii component (divided by `a²`):
`(Ḣ + 3H²)φ − ½ f + Hφ̇ − φ̈ − 3Hφ̇ = κ² p`; adding (C)-as-equation `E00 = 0`
gives
`−2 φ Ḣ = κ²(ρ + p) + φ̈ − H φ̇`                                         (D)
(De Felice–Tsujikawa (2.16)).  Both (C) and (D) were checked symbolically with sympy from the
Christoffel symbols / Ricci tensor of flat FLRW.

**Transformation to the convention used here** (`R = −R_c`, `F(R) = −f(−R)`):
`φ = F′(R)`, `φ R_c − f = F′·(−R) + F = F − R F′`,
`φ̇ = F″(R) Ṙ`, `φ̈ = F‴(R) Ṙ² + F″(R) R̈`. With `κ² = 1`, `p = 0`:
* (C) ↦ `3 F′ H² = ρ + ½(F − R F′) − 3 H F″ Ṙ`;
* (D) ↦ `−2 F′ Ḣ = ρ + F‴ Ṙ² + F″ R̈ − H F″ Ṙ`.
The literature usually divides (C) by `F′` (`H² = ρ/(3F′) + ρ_curv/3`, Capozziello et al.);
we keep the multiplied-through form to avoid junk division by `F′ = 0`.
-/

namespace Work.Fidelity.BlindFR

open Real Filter Topology

/-- Specification of the Ricci scalar of a spatially flat FLRW metric with scale factor `a`
(function of cosmic time), in the **negative** convention: `Rc a t = −6 (ä/a + (ȧ/a)²)`,
so that de Sitter (`a = c·e^{ht}`) has `R = −12 h²`.  In the common convention
(`R_c = +6(ä/a + (ȧ/a)²)`) this is `R = −R_c`.

* `law` determines `Rc a t` whenever `a(t) > 0` and `a` is twice differentiable at `t`, given
  as: `a` has derivative `a' s` at every `s` near `t`, and `a'` has derivative `a''t` at `t`
  (explicit derivative functions, so no `deriv` junk values enter).
* anchors: de Sitter, radiation `a = t^{1/2}` (`R = 0`, conformal/traceless source),
  matter `a = t^{2/3}` (`R = −4/(3t²)`; in common convention `R_c = 4/(3t²) = ρ` for
  Einstein–de Sitter with `κ² = 1`, as `R_c = κ²(ρ − 3p)`).
* invariances: rescaling `a ↦ c·a` (`c > 0`), and time translation. -/
structure RicciFlatFLRWSpec (Rc : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Determining law: `R = −6 (ä/a + (ȧ/a)²)`. -/
  law : ∀ (a a' a'' : ℝ → ℝ) (t : ℝ), 0 < a t →
    (∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) → HasDerivAt a' (a'' t) t →
    Rc a t = -6 * (a'' t / a t + (a' t / a t) ^ 2)
  /-- de Sitter anchor: `a = c·e^{h t}` has `R = −12 h²`. -/
  deSitter : ∀ (c h t : ℝ), 0 < c → Rc (fun s => c * Real.exp (h * s)) t = -12 * h ^ 2
  /-- Radiation anchor: `a = t^{1/2}` has `R = 0` for `t > 0`. -/
  radiation : ∀ t : ℝ, 0 < t → Rc (fun s => s ^ (1 / 2 : ℝ)) t = 0
  /-- Matter (Einstein–de Sitter) anchor: `a = t^{2/3}` has `R = −4/(3t²)` for `t > 0`. -/
  matter : ∀ t : ℝ, 0 < t → Rc (fun s => s ^ (2 / 3 : ℝ)) t = -4 / (3 * t ^ 2)
  /-- Invariance under constant rescaling of the scale factor (normalization of `a` is
  unphysical in flat FLRW). Stated under the same regularity hypotheses as `law`. -/
  scale_invariant : ∀ (a a' a'' : ℝ → ℝ) (c t : ℝ), 0 < c → 0 < a t →
    (∀ᶠ s in 𝓝 t, HasDerivAt a (a' s) s) → HasDerivAt a' (a'' t) t →
    Rc (fun s => c * a s) t = Rc a t
  /-- Invariance under time translation. Stated under the regularity hypotheses of `law`
  at the shifted time `t + τ`. -/
  time_translation : ∀ (a a' a'' : ℝ → ℝ) (τ t : ℝ), 0 < a (t + τ) →
    (∀ᶠ s in 𝓝 (t + τ), HasDerivAt a (a' s) s) → HasDerivAt a' (a'' (t + τ)) (t + τ) →
    Rc (fun s => a (s + τ)) t = Rc a (t + τ)

/-- Hubble rate `H(t) = ȧ/a`. -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Matter (dust) density at time `t`, for dust whose present (`t = t₀`) density parameter is
`Ω`, measured relative to the **GR** critical density with `κ² = 1`, i.e.
`ρ_crit = 3 H₀²` with `H₀ = ȧ(t₀)/a(t₀)` (from `3H² = κ²ρ`).

Closed form: `ρ(t) = 3 H₀² Ω (a(t₀)/a(t))³`.
Why: dust has `p = 0`; in metric F(R) gravity matter is minimally coupled, so `∇^μ T_μν = 0`
still holds (the geometric side is identically divergence free by the generalized Bianchi
identity), giving `ρ̇ + 3H(ρ + p) = 0`, i.e. `ρ a³ = const`, and `ρ(t₀) = Ω ρ_crit`.
Note: `Ω` is *not* the fraction of the F(R) "effective" critical density `3F′(R₀)H₀²`;
it is the GR-normalized parameter. -/
noncomputable def DustDensity (Ω : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  3 * (deriv a t₀ / a t₀) ^ 2 * Ω * (a t₀ / a t) ^ 3

/-- The 00 (Friedmann / constraint) component of the metric F(R) field equations in flat FLRW,
dust source, `κ² = 1`, **negative-R convention** (de Sitter `R = −12H²`), at time `t`:

`3 F′(R) H² = ρ + ½ (F(R) − R F′(R)) − 3 H F″(R) Ṙ`,

with `H = ȧ/a`, `ρ = DustDensity Ω a t₀ t`, `R = R(t)` supplied by the caller (intended
`R = Rc a`).  Derived from De Felice–Tsujikawa (2.15),
`3F′H² = κ²ρ + ½(F′R_c − f) − 3H d(F′)/dt`, via `R = −R_c`, `F(R) = −f(−R)` (see module
docstring).  Multiplied through by `F′` (no division by `F′`).
Checks: `F = R` gives `3H² = ρ`; `F = R + 2Λ` gives `3H² = ρ + Λ` (ΛCDM). -/
def FRFirstEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) (R : ℝ → ℝ) : Prop :=
  3 * deriv F (R t) * (deriv a t / a t) ^ 2 =
    DustDensity Ω a t₀ t + (F (R t) - R t * deriv F (R t)) / 2
      - 3 * (deriv a t / a t) * deriv^[2] F (R t) * deriv R t

/-- The `Ḣ` equation (00 + ii combination) of metric F(R) gravity in flat FLRW, dust source
(`p = 0`), `κ² = 1`, **negative-R convention**, at time `t`:

`−2 F′(R) Ḣ = ρ + F‴(R) Ṙ² + F″(R) R̈ − H F″(R) Ṙ`,

i.e. `−2F′Ḣ = κ²(ρ + p) + d²F′/dt² − H dF′/dt` (De Felice–Tsujikawa (2.16)), where
`d F′/dt = F″ Ṙ` and `d² F′/dt² = F‴ Ṙ² + F″ R̈` are the same in both sign conventions.
`Ḣ` is written as the derivative of `s ↦ ȧ(s)/a(s)`.  No division by `F′`.
Checks: `F = R` gives the Raychaudhuri equation `−2Ḣ = ρ`; same for `F = R + 2Λ`. -/
def FRSecondEq (Ω : ℝ) (a F : ℝ → ℝ) (t₀ t : ℝ) (R : ℝ → ℝ) : Prop :=
  -2 * deriv F (R t) * deriv (fun s => deriv a s / a s) t =
    DustDensity Ω a t₀ t + deriv^[3] F (R t) * (deriv R t) ^ 2
      + deriv^[2] F (R t) * deriv^[2] R t
      - (deriv a t / a t) * deriv^[2] F (R t) * deriv R t

end Work.Fidelity.BlindFR
