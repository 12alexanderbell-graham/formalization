import Mathlib

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
