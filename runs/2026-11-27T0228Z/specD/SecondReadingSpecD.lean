import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Checked.Trust.SecondReadingSpecD

open Real

/-- Helper (my own): the Hubble rate `a'(t)/a(t)` of a scale factor (expansion rate of `a`). -/
noncomputable def hubbleD (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Helper (my own): the curvature-dependent radial function `sin(√K χ)/√K` (K>0),
`χ` (K=0), `sinh(√(-K) χ)/√(-K)` (K<0); Hogg 1999 §5 with `K` in place of `Ω_k`. -/
noncomputable def sinCurvD (K χ : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * χ) / Real.sqrt K
  else if K = 0 then χ
  else Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)

/-- Item 1. `S K χ` is the FLRW transverse comoving distance function (in units where the
coordinate `χ` is the comoving radial coordinate distance, `K` the curvature constant), Hogg 1999
(astro-ph/9905116) §5 written with `K` for `Ω_k` (sign: `K>0` closed gives a sine).
Determines `S K χ` for every real `K` and `χ`. (Source not opened: web access was refused; written
from memory.) -/
structure TransverseSpecD (S : ℝ → ℝ → ℝ) : Prop where
  /-- Closed case (`K > 0`): `S K χ = sin(√K χ)/√K` (Hogg §5). -/
  closed : ∀ K χ : ℝ, 0 < K → S K χ = Real.sin (Real.sqrt K * χ) / Real.sqrt K
  /-- Flat case (`K = 0`): the identity in `χ` (Hogg §5). -/
  flat : ∀ χ : ℝ, S 0 χ = χ
  /-- Open case (`K < 0`): `S K χ = sinh(√(-K) χ)/√(-K)` (Hogg §5). -/
  open_ : ∀ K χ : ℝ, K < 0 → S K χ = Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)

/-- Item 2. Luminosity distance `D K a t₀ t` for emission at `t`, observation at `t₀`, metric
`−dt² + a²(dr²/(1−K r²)+r² dΩ²)`, `c=1`. Defined by `d_L = (1+z) · a(t₀) · r`, with
`1+z = a(t₀)/a(t)` and `r = S_K(∫_t^{t₀} ds/a(s))` the radial coordinate of the source
(Hogg §7, Weinberg §1.4, Bamba et al. §10). Determines `D K a t₀ t` whenever `t ≤ t₀` and `a` is
continuous and positive on `[t,t₀]` (hence integrable). Sources not opened (web refused). -/
structure LumDistSpecD (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Closed case: `d_L = (a(t₀)²/a(t)) · sin(√K χ)/√K`, `χ = ∫_t^{t₀} ds/a(s)`. -/
  closed : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), 0 < K → t ≤ t₀ →
    ContinuousOn a (Set.Icc t t₀) → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = (a t₀ / a t) * a t₀ *
      (Real.sin (Real.sqrt K * ∫ s in t..t₀, 1 / a s) / Real.sqrt K)
  /-- Flat case: `d_L = (a(t₀)²/a(t)) ∫_t^{t₀} ds/a(s)`. -/
  flat : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ →
    ContinuousOn a (Set.Icc t t₀) → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D 0 a t₀ t = (a t₀ / a t) * a t₀ * ∫ s in t..t₀, 1 / a s
  /-- Open case: `d_L = (a(t₀)²/a(t)) · sinh(√(-K) χ)/√(-K)`. -/
  open_ : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), K < 0 → t ≤ t₀ →
    ContinuousOn a (Set.Icc t t₀) → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = (a t₀ / a t) * a t₀ *
      (Real.sinh (Real.sqrt (-K) * ∫ s in t..t₀, 1 / a s) / Real.sqrt (-K))

/-- Item 3. Angular diameter distance `D K a t₀ t = a(t) · r` with `r = S_K(∫_t^{t₀} ds/a)`
the source's radial coordinate (Hogg §6; equals `d_L/(1+z)²`). Same hypotheses and determined
arguments as item 2. Sources not opened (web refused). -/
structure AngDistSpecD (D : ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Closed case: `d_A = a(t) · sin(√K χ)/√K`. -/
  closed : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), 0 < K → t ≤ t₀ →
    ContinuousOn a (Set.Icc t t₀) → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = a t *
      (Real.sin (Real.sqrt K * ∫ s in t..t₀, 1 / a s) / Real.sqrt K)
  /-- Flat case: `d_A = a(t) ∫_t^{t₀} ds/a(s)`. -/
  flat : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ →
    ContinuousOn a (Set.Icc t t₀) → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D 0 a t₀ t = a t * ∫ s in t..t₀, 1 / a s
  /-- Open case: `d_A = a(t) · sinh(√(-K) χ)/√(-K)`. -/
  open_ : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ), K < 0 → t ≤ t₀ →
    ContinuousOn a (Set.Icc t t₀) → (∀ s ∈ Set.Icc t t₀, 0 < a s) →
    D K a t₀ t = a t *
      (Real.sinh (Real.sqrt (-K) * ∫ s in t..t₀, 1 / a s) / Real.sqrt (-K))

/-- Item 4. Flat ΛCDM (Aviles et al. 2012, before Eq. (15)): `E(z)² = (H(z)/H₀)² = Ω(1+z)³ + 1 − Ω`,
with `1+z = a(t₀)/a(t)` and `H = a'/a`. Read here at all times `t`: `a` positive and differentiable
everywhere, `H(t₀) > 0` (expanding now; my own side condition so the sign of `H` is fixed at `t₀`),
and the squared relation for all `t`. Decides the condition for every `a`, `Ω`, `t₀`.
Source not opened (web refused). -/
structure FlatLCDMSpecD (P : ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- `P Ω a t₀` iff `a>0`, differentiable everywhere, `H(t₀)>0`, and
  `H(t)² = H(t₀)² (Ω (a(t₀)/a(t))³ + 1 − Ω)` for all `t`. -/
  iff_ : ∀ (Ω : ℝ) (a : ℝ → ℝ) (t₀ : ℝ),
    P Ω a t₀ ↔
      ((∀ t, 0 < a t ∧ DifferentiableAt ℝ a t) ∧ 0 < hubbleD a t₀ ∧
        ∀ t, (hubbleD a t) ^ 2 =
          (hubbleD a t₀) ^ 2 * (Ω * (a t₀ / a t) ^ (3 : ℝ) + (1 - Ω)))

/-- Item 5. Flat universe of dust and CPL dark energy, `w(z) = w₀ + wₐ z/(1+z)`
(Capozziello–Lazkoz–Salzano 2011, Eq. (17)):
`E(z)² = Ω(1+z)³ + (1−Ω)(1+z)^{3(1+w₀+wₐ)} exp(−3wₐ z/(1+z))`, with `1+z = a(t₀)/a(t)`,
`z/(1+z) = 1 − a(t)/a(t₀)`, `H=a'/a`. Same reading and determined arguments as item 4.
Source not opened (web refused); the formula is the standard integration of `w(z)`. -/
structure FlatCPLSpecD (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- `P Ω w₀ wₐ a t₀` iff `a>0` differentiable, `H(t₀)>0`, and for all `t`
  `H² = H₀² (Ω(1+z)³ + (1−Ω)(1+z)^{3(1+w₀+wₐ)} exp(−3 wₐ (1 − a/a₀)))`. -/
  iff_ : ∀ (Ω w₀ wₐ : ℝ) (a : ℝ → ℝ) (t₀ : ℝ),
    P Ω w₀ wₐ a t₀ ↔
      ((∀ t, 0 < a t ∧ DifferentiableAt ℝ a t) ∧ 0 < hubbleD a t₀ ∧
        ∀ t, (hubbleD a t) ^ 2 =
          (hubbleD a t₀) ^ 2 *
            (Ω * (a t₀ / a t) ^ (3 : ℝ) +
              (1 - Ω) * (a t₀ / a t) ^ (3 * (1 + w₀ + wₐ)) *
                Real.exp (-3 * wₐ * (1 - a t / a t₀))))

/-- Item 6. Curvature parameter in the luminosity-distance cosmography of Bamba et al. §10:
`k = K/(a(t₀)² H₀²)` with `H₀ = a'(t₀)/a(t₀)`; chosen sign: positive for closed, so that it enters
as `+k` in the `z²` coefficient `−(1/6)(1 − q₀ − 3q₀² + j₀ + k)`. UNVERIFIED: source not opened
(web refused); the source may instead use `Ω_k = −K/(a₀H₀)²`. Determined where `a(t₀) ≠ 0`,
`a` differentiable at `t₀` and `a'(t₀) ≠ 0`. -/
structure CurvParamSpecD (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- `k K a t₀ = K / (a(t₀)² H₀²)`. -/
  formula : ∀ (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ), a t₀ ≠ 0 → DifferentiableAt ℝ a t₀ →
    hubbleD a t₀ ≠ 0 →
    k K a t₀ = K / ((a t₀) ^ 2 * (hubbleD a t₀) ^ 2)

/-- Item 7. Ricci scalar of flat FLRW with signature `(−,+,+,+)`:
`R = 6(Ḣ + 2H²) = 6(ä/a + ȧ²/a²)` (Bamba et al. §11, `R = 6Ḣ + 12H²`, from memory, source not
opened). Determined where `a(t) ≠ 0`, `a` differentiable near `t` and `a'` differentiable at `t`. -/
structure RicciFlatSpecD (R : (ℝ → ℝ) → ℝ → ℝ) : Prop where
  /-- Through the Hubble rate: `R = 6 (dH/dt + 2 H²)`. -/
  hubble_form : ∀ (a : ℝ → ℝ) (t : ℝ), a t ≠ 0 → (∀ᶠ s in nhds t, DifferentiableAt ℝ a s) →
    DifferentiableAt ℝ (deriv a) t →
    R a t = 6 * (deriv (hubbleD a) t + 2 * (hubbleD a t) ^ 2)
  /-- Through `a`: `R = 6 (a''/a + (a'/a)²)` (consequence of the same formula). -/
  scale_form : ∀ (a : ℝ → ℝ) (t : ℝ), a t ≠ 0 → (∀ᶠ s in nhds t, DifferentiableAt ℝ a s) →
    DifferentiableAt ℝ (deriv a) t →
    R a t = 6 * (deriv (deriv a) t / a t + (deriv a t / a t) ^ 2)

end Checked.Trust.SecondReadingSpecD
