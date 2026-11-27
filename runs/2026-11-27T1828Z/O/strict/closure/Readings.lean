import Mathlib

/-! # Target O, family O64 (strict inverse-first-power paper): the three blind readings of run 2026-11-27T1828Z,
concatenated unchanged apart from their own `import Mathlib` lines, so a closure can import them as one module. -/


/-!
# Blind reading A of O64b: a strict inverse-first-power bound for univalent functions

Reading of Theorem 1.1 (uniform inverse-first-power bound, the consequence for the bounded
universal integral-means spectrum at exponent minus one, and the failure of Kraetzer's
conjectured formula). All definitions are written from the abstract and introduction.
-/

open Complex Filter Topology Set

namespace ReaderA

/-- The open unit disk `𝔻 = {z ∈ ℂ : |z| < 1}`. -/
def DD : Set ℂ := Metric.ball (0 : ℂ) 1

/-- The normalized schlicht class `𝒮`: injective holomorphic maps `f : 𝔻 → ℂ` with
`f 0 = 0` and `f' 0 = 1`. A map on the disk is modelled as a function `ℂ → ℂ` whose values
outside `𝔻` are irrelevant; holomorphy is `DifferentiableOn ℂ f 𝔻` (𝔻 is open, so `deriv f z`
is the complex derivative at every `z ∈ 𝔻`). -/
def SSS : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f DD ∧ InjOn f DD ∧ f 0 = 0 ∧ deriv f 0 = 1}

/-- The subclass `𝒮_b` of maps with bounded image `f(𝔻)` (the bound may depend on `f`). -/
def SSSb : Set (ℂ → ℂ) :=
  {f | f ∈ SSS ∧ Bornology.IsBounded (f '' DD)}

/-- The integral mean
`M_p[f'](r) = (1/(2π)) ∫_{-π}^{π} |f'(r e^{iθ})|^p dθ`. -/
noncomputable def M (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ θ in (-Real.pi)..Real.pi, ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ p

/-- The limiting exponent
`β_f(p) = limsup_{r ↑ 1} log M_p[f'](r) / log (1/(1-r))`, taken in `EReal`
(left limit `r → 1⁻`). -/
noncomputable def beta (f : ℂ → ℂ) (p : ℝ) : EReal :=
  limsup (fun r : ℝ => ((Real.log (M p f r) / Real.log (1 / (1 - r)) : ℝ) : EReal)) (𝓝[<] 1)

/-- The bounded universal integral-means spectrum `B_b(p) = sup_{f ∈ 𝒮_b} β_f(p)`, in `EReal`. -/
noncomputable def Bb (p : ℝ) : EReal :=
  ⨆ f ∈ SSSb, beta f p

/-- Kraetzer's conjectured spectrum: `p^2/4` for `|p| ≤ 2`, `|p| - 1` for `|p| ≥ 2`
(the two branches agree at `|p| = 2`). -/
noncomputable def kraetzer (p : ℝ) : ℝ :=
  if |p| ≤ 2 then p ^ 2 / 4 else |p| - 1

/-- Theorem 1.1 (Uniform inverse-first-power bound), all three assertions:
(i) there are constants `0 < ε < 1/4` and `C < ∞` with
`M_{-1}[f'](r) ≤ C (1-r)^{-1/4+ε}` for every `f ∈ 𝒮` and every `1/2 ≤ r < 1`;
(ii) consequently `B_b(-1) < 1/4`;
(iii) Kraetzer's conjectured identity `B_b(p) = kraetzer p` (for all real `p`) is false. -/
theorem reading_theorem_1_1 :
    (∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ f ∈ SSS, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
        M (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
    Bb (-1) < ((1 / 4 : ℝ) : EReal) ∧
    ¬ (∀ p : ℝ, Bb p = ((kraetzer p : ℝ) : EReal)) := sorry

/-- An unfolded form of the consequence `B_b(-1) < 1/4`, avoiding the `EReal` supremum:
there is a real `c < 1/4` bounding every `β_f(-1)`, `f ∈ 𝒮_b`. (Equivalent to the `EReal`
statement in `reading_theorem_1_1`, since `𝒮_b` is nonempty.) -/
theorem reading_Bb_lt_unfolded :
    ∃ c : ℝ, c < 1 / 4 ∧ ∀ f ∈ SSSb, beta f (-1) ≤ (c : EReal) := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES (reader A)

1. Maps on the disk. `f : 𝔻 → ℂ` is modelled as `f : ℂ → ℂ` with all hypotheses restricted
   to `DD = Metric.ball 0 1`. Holomorphic = `DifferentiableOn ℂ f DD`; injective =
   `InjOn f DD`; normalization `f 0 = 0`, `deriv f 0 = 1`. Since DD is open and f is
   differentiable there, `deriv f z` for `z ∈ DD` is the genuine derivative (no junk `deriv`).
   For `1/2 ≤ r < 1` (and for every `0 ≤ r < 1`) the circle `|z| = r` lies in DD, so every
   `deriv f` value used in `M` is a genuine derivative.

2. `|f'|^p` uses `Real.rpow` with base `‖f'(z)‖ ≥ 0` (never a negative base). For `p = -1`
   a zero base would give the Mathlib junk value `0 ^ (-1) = 0`; the text remarks (and it is a
   theorem, not an extra hypothesis) that the derivative of a univalent map never vanishes, so
   on the circles used the base is positive. I did not add `deriv f z ≠ 0` as a hypothesis,
   to stay literal.

3. Integral. `∫ θ in (-π)..π` is Mathlib's interval integral. For `f ∈ 𝒮` and `0 ≤ r < 1` the
   integrand `θ ↦ ‖f'(r e^{iθ})‖^p` is continuous (f' is holomorphic and nonvanishing on the
   compact circle), hence integrable, so no `∫ = 0` junk occurs.

4. `log M_p[f'](r)`: `M_p > 0` for `f ∈ 𝒮` (continuous positive integrand), so `Real.log` is
   applied to a positive number. `log (1/(1-r)) > 0` for `0 < r < 1`, so the division is not
   by zero on the relevant punctured neighbourhood of 1 (only values near `1⁻` matter for the
   limsup).

5. limsup and sup. `β_f(p)` could a priori be `+∞`, so I take the limsup in `EReal`
   (complete lattice; `Filter.limsup` there is the true limsup, no junk from unboundedness),
   along `𝓝[<] 1` (r ↑ 1 from the left). `B_b(p)` is the `EReal` supremum over `𝒮_b`, which is
   nonempty (the identity map belongs to it), so it is not the junk `⊥` of an empty sup; a
   value `⊤` would be the genuine "infinite" spectrum and is correctly excluded by
   `B_b(-1) < 1/4`. To remove any doubt about `⊤/⊥`, `reading_Bb_lt_unfolded` restates the
   consequence as "some real `c < 1/4` bounds every `β_f(-1)`".

6. "C < ∞": read as `C` being a real number (no sign condition is stated; none imposed).
   The exponent `-1/4 + ε` is a real exponent applied to `1 - r > 0` (no negative base).

7. Kraetzer's identity. The displayed formula is a claim about all real `p`; "is false" is
   read as `¬ ∀ p, B_b(p) = kraetzer(p)` (in particular it fails at `p = -1`, where the formula
   would give `1/4`). The overlap `|p| = 2` is harmless since both branches give 1; I use the
   first branch for `|p| ≤ 2`.

8. The text's quantifier order "there exist constants ... such that ... for every f and every
   r" is kept: ε and C are uniform in f and r.
-/


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
