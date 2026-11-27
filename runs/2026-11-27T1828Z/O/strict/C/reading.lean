import Mathlib

open Complex Filter Topology

namespace ReaderC

/-!
# Blind reading C, family O, paper O64b: strict inverse-first-power bound

Definitions follow the abstract and introduction only. The open unit disk is
`Metric.ball 0 1`; the normalized schlicht class and its bounded subclass are
written as sets of functions `ℂ → ℂ` whose restriction to the disk is used.
The exponent functional is an `EReal`-valued limsup, and the supremum is taken
in `EReal`, so that no real-valued `sSup` or `limsup` junk occurs.
-/

/-- The open unit disk `𝔻`. -/
def disk : Set ℂ := Metric.ball 0 1

/-- The normalized schlicht class `𝒮`: injective holomorphic maps on the disk with
`f 0 = 0` and `f' 0 = 1`. Functions outside the disk are not constrained. -/
def SSS : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f disk ∧ Set.InjOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1}

/-- The bounded subclass `𝒮_b`: maps in `𝒮` whose image of the disk is bounded. -/
def SSSb : Set (ℂ → ℂ) :=
  {f | f ∈ SSS ∧ Bornology.IsBounded (f '' disk)}

/-- `M_p[f'](r) = (1/(2π)) ∫_{-π}^{π} |f'(r e^{iθ})|^p dθ`. -/
noncomputable def Mp (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ θ in (-Real.pi)..Real.pi,
      ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ p

/-- `β_f(p) = limsup_{r ↑ 1} log M_p[f'](r) / log(1/(1-r))`, valued in `EReal`. -/
noncomputable def betaF (p : ℝ) (f : ℂ → ℂ) : EReal :=
  Filter.limsup
    (fun r : ℝ => ((Real.log (Mp p f r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

/-- `B_b(p) = sup_{f ∈ 𝒮_b} β_f(p)`, valued in `EReal`. -/
noncomputable def Bb (p : ℝ) : EReal :=
  sSup ((fun f => betaF p f) '' SSSb)

/-- Kraetzer's conjectured spectrum: `p^2/4` for `|p| ≤ 2` and `|p| - 1` for `|p| ≥ 2`. -/
noncomputable def kraetzer (p : ℝ) : ℝ :=
  if |p| ≤ 2 then p ^ 2 / 4 else |p| - 1

/-- Theorem 1.1 of O64b: the uniform bound with constants `0 < ε < 1/4` and `C`,
the consequence `B_b(-1) < 1/4`, and the falsity of Kraetzer's identity. -/
theorem reading_O64b_thm11 :
    (∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ f ∈ SSS, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
        Mp (-1) f r ≤ C * (1 - r) ^ (-1 / 4 + ε)) ∧
    Bb (-1) < ((1 / 4 : ℝ) : EReal) ∧
    ¬ (∀ p : ℝ, Bb p = ((kraetzer p : ℝ) : EReal)) := by
  sorry

/-!
## Ambiguities and choices (reader C, O64b)

1. Domain of maps. The text says `f : 𝔻 → ℂ`. I took `f : ℂ → ℂ` and used only its
   restriction to `Metric.ball 0 1`. Holomorphy is `DifferentiableOn ℂ f disk`, which on an
   open set is holomorphy; injectivity is `Set.InjOn f disk`. Values outside the disk are
   irrelevant to every definition: `deriv` at points of the disk is local, and the image
   condition is taken on the disk only.
2. Derivative nonvanishing. The text says the derivative never vanishes for univalent maps.
   I did not add this as a hypothesis. For `f ∈ SSS` it is a theorem, not a convention, so
   `Mp` is only ever evaluated where `‖deriv f ·‖ > 0`; for the real power at base `0` Mathlib
   gives `0 ^ p = 0` for `p ≠ 0` (junk), which is never reached on `SSS`.
3. `Mp` on the circle. `r * exp(iθ)` with `r` real, `0 ≤ r < 1`, and the normalized integral
   `(2π)⁻¹ ∫_{-π}^{π}` as an interval integral. For `f ∈ SSS` the integrand is continuous on
   the circle of radius `r`, hence integrable, so the interval integral is the Lebesgue
   integral and no `∫`-of-nonintegrable junk occurs. For `r` outside `[0,1)` the value is
   unused (the limsup is taken at `1` from the left).
4. Logarithms. `Real.log (Mp p f r)` is positive-argument on `SSS` (positive integrand). The
   denominator `Real.log` of the reciprocal of `1 - r` is positive for `r` in the open interval
   from zero to one, so no division-by-zero junk
   occurs in the limsup, whose filter `𝓝[<] 1` only sees `r` close to `1`.
5. limsup and sup in `EReal`. `β_f(p)` is `Filter.limsup` in `EReal`, so an unbounded
   sequence of values gives `⊤` rather than the real-valued junk `0`. `B_b(p)` is `sSup` in
   `EReal` of the image of `SSSb`; this set is nonempty (it contains `z ↦ z`), so the supremum
   is not the empty-set value `⊥`. Values `⊤`/`⊥` are kept in the statement rather than
   removed, so the bound at minus one, compared with the coerced quarter, is a genuine comparison in `EReal`.
6. The power `(1 - r)` raised to the real exponent (minus a quarter plus `ε`) is `Real.rpow` with positive
   base (since `r < 1`). The exponent is written as the sum of the negative quarter and `ε`.
7. The constants. There exist real numbers `ε` and `C` with `ε` strictly positive and strictly
   below one quarter, and `C` real. `C < ∞` in the text is the same as `C : ℝ`. The bound is
   for all `f ∈ SSS` (not only `SSSb`), as the text states, and for all `r` with
   one half at most `r` and `r < 1`.
8. The consequence `B_b(-1)` is strictly below one quarter, written as the `EReal` inequality
   with the coercion of the real number one quarter.
9. Kraetzer's identity. Written as `Bb p = (kraetzer p : EReal)` for all real `p`, with
   `kraetzer` the piecewise formula in the text (the case with absolute value at most two is
   p squared over four, the case with absolute value at least two is the absolute value minus
   one; the two cases agree at the boundary). The theorem says the identity fails (for some
   `p`); the text's claim is that it fails at `p = -1`, which is what the bound gives. I did not
   write the stronger "fails at p = -1" form; it follows from the same inequality.
10. Not formalized: the phrase "the proof gives existence of a positive gap but does not
   evaluate it" (no numerical content claimed) and the introductory remarks on Beliaev and
   Kraetzer's thesis (bibliographic).
11. Mathlib names used: `Filter.limsup`, `𝓝[<]`, `intervalIntegral` notation `∫ θ in a..b`,
   `Complex.exp`, `Bornology.IsBounded`, `Metric.ball`, `Set.InjOn`, `DifferentiableOn`.
-/

end ReaderC
