import Mathlib

open Complex MeasureTheory Filter Topology

namespace ReaderB

/-- The normalized schlicht class `𝒮`: injective holomorphic `f : 𝔻 → ℂ`, `f 0 = 0`, `f'(0) = 1`.
Maps are modelled as total functions `ℂ → ℂ`; only their values on the open unit disk matter. -/
def IsSchlicht (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball 0 1) ∧ Set.InjOn f (Metric.ball 0 1) ∧
    f 0 = 0 ∧ deriv f 0 = 1

/-- `𝒮_b`: schlicht maps with bounded image (the bound may depend on `f`). -/
def IsSchlichtBounded (f : ℂ → ℂ) : Prop :=
  IsSchlicht f ∧ ∃ R : ℝ, ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ ≤ R

/-- `M_p[f'](r) = (1/(2π)) ∫_{-π}^{π} |f'(r e^{iθ})|^p dθ`. -/
noncomputable def intMean (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (-Real.pi)..Real.pi, ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ p

/-- `β_f(p) = limsup_{r ↑ 1} log M_p[f'](r) / log (1/(1-r))`, as an extended real. -/
noncomputable def beta (f : ℂ → ℂ) (p : ℝ) : EReal :=
  Filter.limsup
    (fun r : ℝ => ((Real.log (intMean p f r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

/-- `B_b(p) = sup_{f ∈ 𝒮_b} β_f(p)`, in `EReal`. -/
noncomputable def Bb (p : ℝ) : EReal :=
  ⨆ f : {f : ℂ → ℂ // IsSchlichtBounded f}, beta f.1 p

/-- Kraetzer's predicted spectrum. -/
noncomputable def kraetzer (p : ℝ) : ℝ :=
  if |p| ≤ 2 then p ^ 2 / 4 else |p| - 1

theorem readingStrictMain :
    (∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < C ∧
      ∀ f : ℂ → ℂ, IsSchlicht f → ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
        intMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
    Bb (-1) < ((1 / 4 : ℝ) : EReal) ∧
    ¬ (∀ p : ℝ, Bb p = ((kraetzer p : ℝ) : EReal)) := sorry

/-
Ambiguities and choices.

* Maps: total functions `ℂ → ℂ` with holomorphy, injectivity, `f 0 = 0`, `deriv f 0 = 1` required on
  the open unit ball; `deriv f` is only evaluated at points `r e^{iθ}` with `r < 1`, i.e. inside the
  ball, where `f` is differentiable (the ball is open), so no `deriv` junk.
* Integrals: for a schlicht `f` the derivative is continuous and never zero on the disk, so the
  integrand `|f'|^p` is continuous and positive on the circle of radius `r < 1`, hence
  integrable and `M_p > 0`; `rpow` is applied to the nonnegative base `‖f'‖`, and `Real.log`
  is applied to a positive number (`M_p`, and `1/(1-r)` for `0 < r < 1`). For non-schlicht `f`
  the quantities are junk, but they are only used for `f` in the class.
* `beta`, `Bb` are taken in `EReal` so the limsup and the sup are always meaningful (they cannot
  be junk for unboundedness); `Bb` is a sup over a nonempty index type (the identity is in `𝒮_b`).
  The claim `Bb (-1) < 1/4` in `EReal` also says it is finite from above; it is bounded below by `β_id`.
* `r ↑ 1` is the filter `𝓝[<] 1` on `ℝ`.
* Theorem 1.1: constants `ε`, `C` real with `0 < ε < 1/4`, `C` finite; I wrote `0 < C` (the
  text only says `C < ∞`; positivity is harmless since the left side is positive). The exponent
  `-1/4 + ε` is applied to the positive base `1 - r`.
* The statement "Kraetzer's identity is false" is `¬ ∀ p, B_b p = kraetzer p`; the conjecture
  for all real `p` (both cases, `|p| ≤ 2` quadratic, `|p| ≥ 2` linear; the overlap at `|p|=2` agrees).
* "Consequently `B_b(-1) < 1/4`" is included as the second conjunct, not derived; Kraetzer's value at
  `p = -1` is `1/4`, so the third conjunct would follow from the second, and I kept all three as the
  text asserts them.
-/

end ReaderB
