/- Copied verbatim (code unchanged) from `runs/2026-11-27T0228Z/specE/SecondReadingSpecE.lean`, written by blind reader E (Sonnet subagent, brief `runs/2026-11-27T0228Z/specE/briefE.md`; written from memory, no source opened). Agreement with the program's pinned definitions: `Checked/Trust/SpecAgreementEF.lean`. -/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Checked.Trust.SecondReadingSpecE

open MeasureTheory Set

/-- Critical point of an isotherm `p` (pressure against molar volume): the standard van der Waals
condition (Poling-Prausnitz-O'Connell ch. 4), namely that the isotherm has a horizontal inflection
at `v`: `(∂p/∂v)_T = 0` and `(∂²p/∂v²)_T = 0`. -/
structure CriticalSpecE (P : (ℝ → ℝ) → ℝ → Prop) : Prop where
  /-- For every isotherm `p` and volume `v`: `P p v` holds iff `p` is differentiable at `v`, its
  derivative is differentiable at `v` (regularity: my own explicit addition, since Mathlib's `deriv`
  is `0` at non-differentiable points), and the first and second derivatives vanish at `v`.
  Two-sided derivatives, `v` being an interior volume. -/
  iff_ : ∀ (p : ℝ → ℝ) (v : ℝ), P p v ↔
    (DifferentiableAt ℝ p v ∧ DifferentiableAt ℝ (deriv p) v ∧
      deriv p v = 0 ∧ deriv (deriv p) v = 0)

/-- Vapour-liquid coexistence by Maxwell's equal-area construction (Callen ch. 9): the liquid and
gas volumes have the same pressure `ps` on the isotherm, and the areas above and below the line
`p = ps` between them are equal, i.e. `∫_{vl}^{vg} (p v - ps) dv = 0`. -/
structure CoexistenceSpecE (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) : Prop where
  /-- `P p vl vg ps` iff `vl < vg` (strict ordering: my choice, the source names the liquid as the
  smaller volume), `p vl = ps`, `p vg = ps`, `p` is interval integrable on `[vl, vg]` (regularity:
  my own addition so that the integral is meaningful), and the equal-area condition
  `∫ v in vl..vg, (p v - ps) = 0` holds. No stability (negative slope) condition is imposed, as
  the equal-area statement in the source does not include it. -/
  iff_ : ∀ (p : ℝ → ℝ) (vl vg ps : ℝ), P p vl vg ps ↔
    (vl < vg ∧ p vl = ps ∧ p vg = ps ∧ IntervalIntegrable p volume vl vg ∧
      ∫ v in vl..vg, (p v - ps) = 0)

/-- Undamped unforced Duffing oscillator `x'' + k x + β x³ = 0` with unit mass
(Kovacic-Brennan ch. 1), as an initial value problem on `[0, T]`. -/
structure DuffingSpecE (P : ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) : Prop where
  /-- `P k β x₀ v₀ T x` iff there is a velocity function `w` such that, at every `t ∈ [0, T]`,
  `x` has derivative `w t` and `w` has derivative `-(k x t + β (x t)^3)` (both as derivatives within
  `[0, T]`, so one-sided at the end points `0` and `T`: my choice of regularity), with
  `x 0 = x₀` and `w 0 = v₀`. The existential velocity avoids needing `deriv`, and the statement
  is meant for every `T` (for `T < 0` the interval is empty and only the initial values remain). -/
  iff_ : ∀ (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ), P k β x₀ v₀ T x ↔
    ∃ w : ℝ → ℝ,
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt x (w t) (Icc 0 T) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt w (-(k * x t + β * (x t) ^ 3)) (Icc 0 T) t) ∧
      x 0 = x₀ ∧ w 0 = v₀

/-- Mass-action equations of the Michaelis-Menten mechanism `E + S ⇌ C → E + P`
(Segel-Slemrod 1989): `s' = -k₁ s e + k₋₁ c`, `e' = -k₁ s e + (k₋₁ + k₂) c`,
`c' = k₁ s e - (k₋₁ + k₂) c`, `p' = k₂ c`. -/
structure MMSpecE
    (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) :
    Prop where
  /-- `P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p` iff the four equations above hold at every `t ∈ [0, T]`
  as derivatives within `[0, T]` (one-sided at the end points: my choice of regularity), and
  `s 0 = s₀`, `e 0 = e₀`, `c 0 = c₀`, `p 0 = p₀`. Rate of binding is `k₁ s e`, of unbinding
  `km₁ c`, of catalysis `k₂ c` (standard mass action, no stoichiometric factors other than 1). -/
  iff_ : ∀ (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ), P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔
    ((∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt s (-k₁ * s t * e t + km₁ * c t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt e (-k₁ * s t * e t + (km₁ + k₂) * c t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt c (k₁ * s t * e t - (km₁ + k₂) * c t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t) ∧
     s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀)

/-- Mass-action equations of Robertson's network with the numbering fixed in the task:
`A → B` (`k₁`, rate `k₁ [A]`), `B + C → A + C` (`k₂`, rate `k₂ [B][C]`), `2B → B + C`
(`k₃`, rate `k₃ [B]²`, B net change `-1`, C net change `+1`). This gives
`y₁' = -k₁ y₁ + k₂ y₂ y₃`, `y₂' = k₁ y₁ - k₂ y₂ y₃ - k₃ y₂²`, `y₃' = k₃ y₂²`
(Robertson 1966; Hairer-Wanner IV.1, where `k₁ = 0.04`, `k₂ = 1e4`, `k₃ = 3e7`). -/
structure RobSpecE
    (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop where
  /-- `P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃` iff the three equations above hold at every `t ∈ [0, T]`
  as derivatives within `[0, T]` (one-sided at the end points: my choice of regularity), and
  `y₁ 0 = a₀`, `y₂ 0 = b₀`, `y₃ 0 = c₀`. -/
  iff_ : ∀ (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ), P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔
    ((∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * (y₂ t) ^ 2) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt y₃ (k₃ * (y₂ t) ^ 2) (Icc 0 T) t) ∧
     y₁ 0 = a₀ ∧ y₂ 0 = b₀ ∧ y₃ 0 = c₀)

/-- Comoving radial distance travelled by light emitted at `t` and received at `t₀` in an FLRW
model with scale factor `a`, `c = 1` (Hogg 1999 §5; Weinberg §1.4): since `dχ = dt / a(t)` along a
null ray, `χ = ∫_t^{t₀} dt' / a(t')`. -/
structure ComovingSpecE (X : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop where
  /-- Whenever `t ≤ t₀` (my choice: emission not after observation, so the distance is
  nonnegative), `a` is continuous on `[t, t₀]` and positive there (the stated hypothesis on the
  scale factor), `X a t₀ t = ∫ s in t..t₀, 1 / a s`. Nothing is asserted outside these hypotheses. -/
  formula : ∀ (a : ℝ → ℝ) (t₀ t : ℝ), t ≤ t₀ → ContinuousOn a (Icc t t₀) →
    (∀ s ∈ Icc t t₀, 0 < a s) → X a t₀ t = ∫ s in t..t₀, 1 / a s

end Checked.Trust.SecondReadingSpecE
