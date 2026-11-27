/- Copied verbatim (code unchanged) from `runs/2026-11-27T0228Z/specF/SecondReadingSpecF.lean`, written by blind reader F (Sonnet subagent, brief `runs/2026-11-27T0228Z/specF/briefF.md`; written from memory, no source opened). Agreement with the program's pinned definitions: `Checked/Trust/SpecAgreementEF.lean`. -/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Set.Basic

namespace Checked.Trust.SecondReadingSpecF

open Set MeasureTheory

/-- Critical point of an isotherm `p` (pressure against molar volume) in the sense used to find the
critical constants of a cubic equation of state (Poling-Prausnitz-O'Connell ch. 4; textbook van der
Waals): the isotherm has a horizontal inflection at `v`, i.e. `(∂p/∂v)_T = 0` and `(∂²p/∂v²)_T = 0`. -/
structure CriticalSpecF (P : (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- `P p v` holds iff `p` is differentiable at `v`, `deriv p` is differentiable at `v` (my addition:
  the source tacitly assumes the isotherm smooth, so that the two derivatives are genuine rather than
  Lean's junk value 0), and the first and second derivatives of `p` at `v` both vanish. -/
  iff_inflection : ∀ (p : ℝ → ℝ) (v : ℝ), P p v ↔
    (DifferentiableAt ℝ p v ∧ DifferentiableAt ℝ (deriv p) v ∧
      deriv p v = 0 ∧ deriv (deriv p) v = 0)

/-- Vapour-liquid coexistence by Maxwell's equal-area construction (Callen ch. 9): at the saturation
pressure `ps` the isotherm takes that value at both the liquid volume `vl` and gas volume `vg`, and the
areas above and below the horizontal line `p = ps` between them are equal. -/
structure CoexistenceSpecF (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) : Prop where
  /-- `P p vl vg ps` holds iff `vl < vg` (my choice: volumes strictly ordered, liquid smaller),
  `p vl = ps`, `p vg = ps`, `p` is interval integrable on `[vl, vg]` (my regularity addition so the
  integral is genuine), and `∫_{vl}^{vg} (p v - ps) dv = 0` (equal areas, i.e. `∫ p = ps (vg - vl)`).
  No positivity of volumes or stability (`p' < 0`) conditions are imposed, as the source's construction
  states none. -/
  iff_equal_area : ∀ (p : ℝ → ℝ) (vl vg ps : ℝ), P p vl vg ps ↔
    (vl < vg ∧ p vl = ps ∧ p vg = ps ∧ IntervalIntegrable p volume vl vg ∧
      ∫ v in vl..vg, (p v - ps) = 0)

/-- Undamped unforced Duffing oscillator, unit mass: `x'' + k x + β x³ = 0` (Kovacic-Brennan ch. 1,
with linear stiffness `k`, cubic stiffness `β`, no damping, no forcing). -/
structure DuffingSpecF (P : ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) : Prop where
  /-- `P k β x₀ v₀ T x` holds iff `0 ≤ T` (my addition) and there are functions `x'`, `x''` such that on
  `[0,T]` `x` has derivative `x'` and `x'` has derivative `x''`, both taken within `[0,T]` (one-sided
  at the end points; my choice, since the source says nothing, so `x` is `C¹` with `x'` differentiable),
  `x 0 = x₀`, `x' 0 = v₀`, and `x'' t = -(k * x t + β * x t ^ 3)` for all `t ∈ [0,T]`. -/
  iff_ode : ∀ (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ), P k β x₀ v₀ T x ↔
    (0 ≤ T ∧ ∃ x' x'' : ℝ → ℝ,
      (∀ t ∈ Icc 0 T, HasDerivWithinAt x (x' t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt x' (x'' t) (Icc 0 T) t) ∧
      x 0 = x₀ ∧ x' 0 = v₀ ∧
      ∀ t ∈ Icc 0 T, x'' t = -(k * x t + β * x t ^ 3))

/-- Full Michaelis-Menten mechanism `E + S ⇌ C → E + P` under mass-action kinetics (Segel-Slemrod 1989):
`s' = -k₁ e s + k₋₁ c`, `e' = -k₁ e s + (k₋₁ + k₂) c`, `c' = k₁ e s - (k₋₁ + k₂) c`, `p' = k₂ c`. -/
structure MMSpecF (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) :
    Prop where
  /-- `P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` holds iff `0 ≤ T` (my addition), the four functions have
  derivatives within `[0,T]` at every `t ∈ [0,T]` (one-sided at the end points; my choice) equal to the
  right-hand sides above (so each is `C¹` on `[0,T]`), and `s 0 = s₀`, `e 0 = e₀`, `c 0 = c₀`,
  `p 0 = p₀`. Rate constants are not required positive and concentrations not required nonnegative. -/
  iff_ode : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ), P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔
    (0 ≤ T ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt s (-k₁ * e t * s t + km₁ * c t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt e (-k₁ * e t * s t + (km₁ + k₂) * c t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt c (k₁ * e t * s t - (km₁ + k₂) * c t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t) ∧
      s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀)

/-- Robertson's (1966) network with this numbering: `A → B` (`k₁`, rate `k₁ [A]`),
`B + C → A + C` (`k₂`, rate `k₂ [B][C]`), `2B → B + C` (`k₃`, rate `k₃ [B]²`, no factor 1/2 in the rate
law; net change `-1` for B and `+1` for C), giving
`y₁' = -k₁ y₁ + k₂ y₂ y₃`, `y₂' = k₁ y₁ - k₂ y₂ y₃ - k₃ y₂²`, `y₃' = k₃ y₂²` (Hairer-Wanner IV.1). -/
structure RobSpecF (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop where
  /-- `P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃` holds iff `0 ≤ T` (my addition), each `yᵢ` has, at every
  `t ∈ [0,T]`, derivative within `[0,T]` (one-sided at the end points; my choice) equal to the
  right-hand sides above, and `y₁ 0 = a₀`, `y₂ 0 = b₀`, `y₃ 0 = c₀`. -/
  iff_ode : ∀ (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ), P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔
    (0 ≤ T ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt y₂
        (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * (y₂ t) ^ 2) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt y₃ (k₃ * (y₂ t) ^ 2) (Icc 0 T) t) ∧
      y₁ 0 = a₀ ∧ y₂ 0 = b₀ ∧ y₃ 0 = c₀)

/-- Comoving radial distance in an FLRW model, `c = 1` (Hogg 1999 §5; Weinberg §1.4): light travels
`dχ = dt / a(t)`, so `X a t₀ t = ∫_t^{t₀} ds / a(s)`. -/
structure ComovingSpecF (X : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Whenever `a` is continuous and positive on the segment between `t` and `t₀` (hypothesis stated in
  the brief), `X a t₀ t = ∫_{t}^{t₀} (a s)⁻¹ ds` (oriented interval integral; for `t > t₀` this is
  negative, my convention, since the source takes `t ≤ t₀`). Nothing is said when the hypothesis fails. -/
  eq_integral : ∀ (a : ℝ → ℝ) (t₀ t : ℝ),
    ContinuousOn a (uIcc t t₀) → (∀ s ∈ uIcc t t₀, 0 < a s) →
    X a t₀ t = ∫ s in t..t₀, (a s)⁻¹

end Checked.Trust.SecondReadingSpecF
