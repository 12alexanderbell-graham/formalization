import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

namespace Checked.Trust.SecondReadingSpecC

open Filter Topology

/-- Helper: the transverse function written out (sine / identity / sinh by the sign of `K`).
Used only inside items 2 and 3 to spell the formula out. -/
noncomputable def transverseFn (K χ : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * χ) / Real.sqrt K
  else if K = 0 then χ
  else Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)

/-- Item 1. `S K χ` is the FLRW transverse comoving distance function (Hogg 1999, §5, with the
curvature constant `K` in place of `Ω_k`, so that the unit-radius-of-curvature factors are
`1/√K`): sine for `K > 0`, identity for `K = 0`, hyperbolic sine for `K < 0`.
Determined for every `K` and every `χ ≥ 0` (a negative radial distance is not constrained). -/
structure TransverseSpecC (S : ℝ → ℝ → ℝ) : Prop where
  /-- Closed case `K > 0`: `S K χ = sin(√K χ)/√K` (Hogg §5). -/
  closed : ∀ K χ : ℝ, 0 < K → 0 ≤ χ → S K χ = Real.sin (Real.sqrt K * χ) / Real.sqrt K
  /-- Flat case `K = 0`: `S 0 χ = χ` (Hogg §5). -/
  flat : ∀ χ : ℝ, 0 ≤ χ → S 0 χ = χ
  /-- Open case `K < 0`: `S K χ = sinh(√(-K) χ)/√(-K)` (Hogg §5). -/
  open_ : ∀ K χ : ℝ, K < 0 → 0 ≤ χ → S K χ = Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)

/-- Item 2. Luminosity distance `D K a t₀ t` (c = 1) of light emitted at `t` and received at `t₀`
in the FLRW metric `-dt² + a² (dr²/(1-K r²) + r² dΩ²)`. Source: Hogg §7, Weinberg §1.4,
Bamba et al. 2012 §10: `d_L = a(t₀) (1+z) r`, where `1+z = a(t₀)/a(t)` and the comoving
coordinate `r = S_K(χ)` with `χ = ∫_t^{t₀} ds / a(s)` (S = sin(√K χ)/√K, χ, sinh(√-K χ)/√-K).
Determined for `t ≤ t₀` with `a` continuous and positive on `[t, t₀]`; nothing else is constrained. -/
structure LumDistSpecC (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Closed: `d_L = (a(t₀)²/a(t)) · sin(√K χ)/√K`, `χ = ∫_t^{t₀} 1/a`. -/
  closed : ∀ K (a : ℝ → ℝ) t₀ t, 0 < K → t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = a t₀ * (a t₀ / a t) *
      (Real.sin (Real.sqrt K * ∫ s in t..t₀, 1 / a s) / Real.sqrt K)
  /-- Flat: `d_L = (a(t₀)²/a(t)) · χ`. -/
  flat : ∀ (a : ℝ → ℝ) t₀ t, t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D 0 a t₀ t = a t₀ * (a t₀ / a t) * ∫ s in t..t₀, 1 / a s
  /-- Open: `d_L = (a(t₀)²/a(t)) · sinh(√(-K) χ)/√(-K)`. -/
  open_ : ∀ K (a : ℝ → ℝ) t₀ t, K < 0 → t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = a t₀ * (a t₀ / a t) *
      (Real.sinh (Real.sqrt (-K) * ∫ s in t..t₀, 1 / a s) / Real.sqrt (-K))

/-- Item 3. Angular diameter distance `D K a t₀ t` for the same data (Hogg §6, Bamba et al.
§10): `d_A = a(t) · r` with `r = S_K(χ)`, `χ = ∫_t^{t₀} 1/a`; equivalently `d_L/(1+z)²`
(Etherington). Determined for `t ≤ t₀`, `a` continuous and positive on `[t, t₀]`. -/
structure AngDistSpecC (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Closed: `d_A = a(t) · sin(√K χ)/√K`. -/
  closed : ∀ K (a : ℝ → ℝ) t₀ t, 0 < K → t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = a t * (Real.sin (Real.sqrt K * ∫ s in t..t₀, 1 / a s) / Real.sqrt K)
  /-- Flat: `d_A = a(t) · χ`. -/
  flat : ∀ (a : ℝ → ℝ) t₀ t, t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D 0 a t₀ t = a t * ∫ s in t..t₀, 1 / a s
  /-- Open: `d_A = a(t) · sinh(√(-K) χ)/√(-K)`. -/
  open_ : ∀ K (a : ℝ → ℝ) t₀ t, K < 0 → t ≤ t₀ → ContinuousOn a (Set.Icc t t₀) →
    (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = a t * (Real.sinh (Real.sqrt (-K) * ∫ s in t..t₀, 1 / a s) / Real.sqrt (-K))

/-- Item 4. Flat ΛCDM (dust + Λ, no radiation), matter parameter `Ω`, present time `t₀`.
Source (as I read it; not opened online): `H(z)² = H₀² [Ω (1+z)³ + 1 - Ω]` with
`H = a'/a`, `1+z = a(t₀)/a(t)`, `H₀ = H(t₀)`. The condition is local: it concerns a
neighbourhood of `t₀` only (a global statement would fail at a big bang / recollapse). I
take the positive root with the sign of `H₀` (my choice). -/
structure FlatLCDMSpecC (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- `P Ω a t₀` holds iff `a(t₀) > 0` and, for all `t` near `t₀`, `a` is positive and
  differentiable with `a'/a = H₀ √(Ω (a(t₀)/a)³ + 1 - Ω)`, `H₀ = a'(t₀)/a(t₀)`. -/
  iff_expansion : ∀ Ω (a : ℝ → ℝ) t₀, P Ω a t₀ ↔
    (0 < a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
      deriv a t / a t = (deriv a t₀ / a t₀) *
        Real.sqrt (Ω * (a t₀ / a t) ^ 3 + (1 - Ω)))

/-- Item 5. Flat universe of dust plus CPL dark energy `w(z) = w₀ + wₐ z/(1+z)`
(Capozziello–Lazkoz–Salzano 2011, Eq. (17), as I recall it; not opened online):
`H(z)² = H₀² [Ω (1+z)³ + (1-Ω)(1+z)^{3(1+w₀+wₐ)} exp(-3 wₐ z/(1+z))]`, with
`1+z = a(t₀)/a(t)`, `z/(1+z) = 1 - a(t)/a(t₀)`. Local near `t₀`, as in item 4. -/
structure FlatCPLSpecC (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- `P Ω w₀ wₐ a t₀` iff `a(t₀) > 0` and near `t₀`, `a` is positive, differentiable and
  `a'/a = H₀ √(Ω (1+z)³ + (1-Ω)(1+z)^{3(1+w₀+wₐ)} exp(-3 wₐ (1 - a/a(t₀))))`. -/
  iff_expansion : ∀ Ω w₀ wₐ (a : ℝ → ℝ) t₀, P Ω w₀ wₐ a t₀ ↔
    (0 < a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧
      deriv a t / a t = (deriv a t₀ / a t₀) *
        Real.sqrt (Ω * (a t₀ / a t) ^ 3 +
          (1 - Ω) * (a t₀ / a t) ^ (3 * (1 + w₀ + wₐ)) *
            Real.exp (-3 * wₐ * (1 - a t / a t₀))))

/-- Item 6. Dimensionless curvature parameter in the cosmographic luminosity-distance expansion
(Bamba et al. 2012 §10; source not opened, written from memory): the combination
`1 - q₀ - 3q₀² + j₀ + k` with `k = K/(a(t₀) H₀)²` (positive for closed universes),
`H₀ = a'(t₀)/a(t₀)`. SIGN CONVENTION UNVERIFIED. Determined when `a` has a derivative at `t₀`,
`a(t₀) ≠ 0` and `H₀ ≠ 0`. -/
structure CurvParamSpecC (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- `k K a t₀ = K / (a(t₀)² H₀²)` with `H₀ = a'(t₀)/a(t₀)`; i.e. `K / a'(t₀)²`. -/
  formula : ∀ K (a : ℝ → ℝ) t₀ (a1 : ℝ), HasDerivAt a a1 t₀ → a t₀ ≠ 0 → a1 ≠ 0 →
    k K a t₀ = K / ((a t₀) ^ 2 * (a1 / a t₀) ^ 2)

/-- Item 7. Ricci scalar of flat FLRW with scale factor `a` in the signature `(-,+,+,+)` convention
of Bamba et al. 2012 §11 (F(R) gravity, around Eq. (11.6), written from memory):
`R = 6 (Ḣ + 2H²) = 6 (ä/a + ȧ²/a²)`, `H = ȧ/a`. Determined where `a(t) ≠ 0` and `a` is twice
differentiable at `t`. -/
structure RicciFlatSpecC (R : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- With `H = a'/a`, `R a t = 6 (H' + 2 H²)`; stated through the derivatives `a1 = a'(t)`,
  `a2 = a''(t)`: `R = 6 (a2/a + (a1/a)²)`. -/
  formula : ∀ (a : ℝ → ℝ) t (a1 a2 : ℝ), HasDerivAt a a1 t → HasDerivAt (deriv a) a2 t →
    a t ≠ 0 → R a t = 6 * (a2 / a t + (a1 / a t) ^ 2)

end Checked.Trust.SecondReadingSpecC
