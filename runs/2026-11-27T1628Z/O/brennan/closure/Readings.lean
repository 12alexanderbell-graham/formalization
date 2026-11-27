import Mathlib

/-! # Target O, family brennan: the three blind readings of run 2026-11-27T1628Z (brief 5b216ff), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Blind reading A of O64, "Brennan's conjecture and sharp inverse-square integral means":
Theorem 1.1 (all four assertions) and Corollary 1.2 (the Koebe function).
-/

namespace ReaderA

open Complex MeasureTheory Filter Topology
open scoped ENNReal

/-- The open unit disk `𝔻 = {z : |z| < 1}`. -/
def UnitDisk : Set ℂ := Metric.ball 0 1

/-- A univalent map on `𝔻`: holomorphic and injective on `𝔻`. Maps `𝔻 → ℂ` are represented by
functions `ℂ → ℂ`; values off `𝔻` play no role in anything below. -/
def UnivalentOnDisk (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f UnitDisk ∧ Set.InjOn f UnitDisk

/-- The normalized schlicht class `𝒮 = {f : 𝔻 → ℂ univalent : f(0) = 0, f'(0) = 1}`. -/
def Schlicht : Set (ℂ → ℂ) :=
  {f | UnivalentOnDisk f ∧ f 0 = 0 ∧ deriv f 0 = 1}

/-- `M_t[f'](r) = (1/2π) ∫_{-π}^{π} |f'(r e^{iθ})|^t dθ`. -/
noncomputable def Mt (t : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  1 / (2 * Real.pi) *
    ∫ θ in (-Real.pi)..Real.pi, ‖deriv f ((r : ℂ) * exp ((θ : ℂ) * I))‖ ^ t

/-- `β_f(t) = limsup_{r ↑ 1} log M_t[f'](r) / log(1/(1-r))`, as an extended real
(the limsup is taken in `EReal`, so it is never a junk value). -/
noncomputable def betaF (f : ℂ → ℂ) (t : ℝ) : EReal :=
  limsup (fun r : ℝ => ((Real.log (Mt t f r) / Real.log (1 / (1 - r)) : ℝ) : EReal)) (𝓝[<] 1)

/-- `B_𝒮(t) = sup_{f ∈ 𝒮} β_f(t)` (in `EReal`). -/
noncomputable def BS (t : ℝ) : EReal :=
  ⨆ f ∈ Schlicht, betaF f t

/-- The Koebe function `z / (1 - z)^2`. -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- Theorem 1.1, assertion 1: uniform inverse-square integral means bound. -/
theorem reading_thm_1_1_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ f ∈ Schlicht, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
      Mt (-2) f r ≤ Cε * (1 - r) ^ (-1 - ε) := sorry

/-- Theorem 1.1, assertion 2: `B_𝒮(-2) = 1`. -/
theorem reading_thm_1_1_BS : BS (-2) = 1 := sorry

/-- Theorem 1.1, assertion 3 (domain form, Brennan's conjecture). -/
theorem reading_thm_1_1_domain
    (W : Set ℂ) (hWo : IsOpen W) (hWc : IsConnected W) (hWsc : SimplyConnectedSpace W)
    (hbdry : (frontier (((↑) : ℂ → OnePoint ℂ) '' W)).Nontrivial)
    (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ W) (hbij : Set.BijOn φ W UnitDisk)
    (s : ℝ) (hs1 : 4 / 3 < s) (hs2 : s < 4) :
    ∫⁻ z in W, (‖deriv φ z‖₊ : ℝ≥0∞) ^ s < ∞ := sorry

/-- Theorem 1.1, assertion 4 (disk form). -/
theorem reading_thm_1_1_disk
    (f : ℂ → ℂ) (hf : UnivalentOnDisk f) (t : ℝ) (ht1 : -2 < t) (ht2 : t < 2 / 3) :
    ∫⁻ w in UnitDisk, (‖deriv f w‖₊ : ℝ≥0∞) ^ t < ∞ := sorry

/-- Corollary 1.2: the Koebe function is in `𝒮` and both endpoint area integrals diverge. -/
theorem reading_cor_1_2_koebe :
    koebe ∈ Schlicht ∧
      ∫⁻ w in UnitDisk, (‖deriv koebe w‖₊ : ℝ≥0∞) ^ (-2 : ℝ) = ∞ ∧
      ∫⁻ w in UnitDisk, (‖deriv koebe w‖₊ : ℝ≥0∞) ^ (2 / 3 : ℝ) = ∞ := sorry

/-- Corollary 1.2, last sentence: the inverse `φ = koebe⁻¹ : koebe(𝔻) → 𝔻` fails area
integrability at `s = 4` and at `s = 4/3`. -/
theorem reading_cor_1_2_inverse
    (φ : ℂ → ℂ) (hφ : ∀ z ∈ UnitDisk, φ (koebe z) = z) :
    ∫⁻ z in koebe '' UnitDisk, (‖deriv φ z‖₊ : ℝ≥0∞) ^ (4 : ℝ) = ∞ ∧
      ∫⁻ z in koebe '' UnitDisk, (‖deriv φ z‖₊ : ℝ≥0∞) ^ (4 / 3 : ℝ) = ∞ := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Maps on 𝔻 are functions `ℂ → ℂ`; "univalent" = `DifferentiableOn ℂ f 𝔻 ∧ InjOn f 𝔻`.
   `f'(0)` is `deriv f 0`, legitimate because f is differentiable on the open disk (no junk).
   The supremum over 𝒮 ranges over functions `ℂ → ℂ`, so many representatives of one map on 𝔻
   occur; β_f depends only on values on 𝔻 (r < 1), so this does not change B_𝒮.

2. M_t[f'](r): `1/(2π) ∫_{-π}^{π} ‖f'(r e^{iθ})‖^t dθ` with `Real.rpow`. For univalent f,
   f' has no zeros in 𝔻, so the base is positive (no `0^t` junk for t < 0), and the integrand
   is continuous on the circle, hence integrable (the interval integral is not the junk 0).
   For f ∈ 𝒮 and 0 < r < 1, M_t > 0, so `Real.log` is applied to a positive number.

3. β_f(t): limsup along `𝓝[<] 1` (r ↑ 1) of `log M_t / log(1/(1-r))`, computed in `EReal`
   to avoid the junk value of a real `limsup` of an unbounded function. Near r = 1 from
   below, 1/(1-r) > 1, so `log(1/(1-r)) > 0` and the division is not by 0. B_𝒮(t) is an
   `iSup` in `EReal` (complete lattice, no junk); `B_𝒮(-2) = 1` is an equality in `EReal`,
   which also asserts finiteness. The "equivalently ... infimum of b" characterization is
   not formalized separately (it is a remark).

4. Uniform bound: `∃ Cε : ℝ` (finite), for all f ∈ 𝒮 and 1/2 ≤ r < 1,
   `M_{-2}[f'](r) ≤ Cε (1-r)^{-1-ε}` with `Real.rpow` of the positive base `1 - r`.

5. Domain form: W ⊆ ℂ a domain = open and connected (`IsConnected` includes nonempty);
   simply connected = Mathlib `SimplyConnectedSpace W` on the subtype. "Boundary in the
   Riemann sphere contains at least two points": the Riemann sphere is `OnePoint ℂ`; the
   boundary is `frontier` of the image of W in `OnePoint ℂ`, required `Nontrivial` (≥ 2
   points). "Conformal bijection φ : W → 𝔻": φ holomorphic on W and `BijOn φ W 𝔻`
   (holomorphic + injective = conformal). `φ'` is `deriv φ`, legitimate on the open set W.

6. Area integrals "< ∞": lower Lebesgue integrals `∫⁻` of `‖·‖₊ ^ s` in `ℝ≥0∞` against Mathlib's
   `volume` on ℂ, which is planar Lebesgue measure dx dy. This avoids the Bochner-integral
   junk value for non-integrable functions, and "= ∞" in Cor 1.2 is literal. `ENNReal.rpow`
   of 0 with negative exponent is ⊤, but derivatives of univalent maps never vanish on 𝔻,
   so this case does not arise on the sets of integration.

7. Disk form: every univalent f (not necessarily normalized), -2 < t < 2/3. The text's
   "Equivalently" links assertions 3 and 4; both are stated as separate theorems.

8. Koebe function `z/(1-z)^2` as a function ℂ → ℂ (at z = 1, Lean's x/0 = 0, but z = 1 is
   outside 𝔻, so irrelevant). Corollary 1.2's displayed claim: `koebe ∈ 𝒮` and both area
   integrals over 𝔻 equal ∞. The final sentence (failure for the inverse at s = 4 and 4/3)
   is stated separately: for any φ with φ ∘ koebe = id on 𝔻, the integrals of
   `|φ'|^4` and `|φ'|^{4/3}` over koebe(𝔻) are ∞. φ is then the inverse on the open set
   koebe(𝔻), hence holomorphic there, so `deriv φ` is not junk.
-/


namespace ReaderB

open MeasureTheory Filter Topology Set

/-- The open unit disk. -/
def DD : Set ℂ := Metric.ball 0 1

/-- `f` is univalent on `D`: holomorphic and injective there. -/
def UnivalentOn (f : ℂ → ℂ) (D : Set ℂ) : Prop := DifferentiableOn ℂ f D ∧ Set.InjOn f D

/-- The normalized schlicht class `𝒮` (functions on `ℂ`, only values on `DD` matter). -/
def SSS : Set (ℂ → ℂ) := {f | UnivalentOn f DD ∧ f 0 = 0 ∧ deriv f 0 = 1}

/-- `M_t[f'](r) = (1/2π) ∫_{-π}^{π} |f'(r e^{iθ})|^t dθ`. -/
noncomputable def M (t : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t

/-- `β_f(t) = limsup_{r↑1} log M_t[f'](r) / log(1/(1-r))`, in `EReal`. -/
noncomputable def beta (f : ℂ → ℂ) (t : ℝ) : EReal :=
  limsup (fun r : ℝ => ((Real.log (M t f r) / Real.log (1 / (1 - r)) : ℝ) : EReal)) (𝓝[<] 1)

/-- `B_𝒮(t) = sup_{f ∈ 𝒮} β_f(t)`, in `EReal`. -/
noncomputable def BS (t : ℝ) : EReal := ⨆ f ∈ SSS, beta f t

/-- Theorem 1.1, all four assertions. -/
theorem readingBrennan :
    -- uniform bound
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ f ∈ SSS, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
        M (-2) f r ≤ C * (1 - r) ^ (-(1 + ε))) ∧
    -- B_S(-2) = 1
    BS (-2) = 1 ∧
    -- domain form
    (∀ W : Set ℂ, IsOpen W → IsConnected W → SimplyConnectedSpace W →
      2 ≤ (frontier (((↑) : ℂ → OnePoint ℂ) '' W)).encard →
      ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ W → Set.BijOn φ W DD →
        ∀ s : ℝ, 4 / 3 < s → s < 4 →
          IntegrableOn (fun z => ‖deriv φ z‖ ^ s) W volume) ∧
    -- disk form
    (∀ f : ℂ → ℂ, UnivalentOn f DD → ∀ t : ℝ, -2 < t → t < 2 / 3 →
        IntegrableOn (fun w => ‖deriv f w‖ ^ t) DD volume) := by
  sorry

/-- The Koebe function. -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- Corollary 1.2. "`= ∞`" is stated as the (nonnegative) lower Lebesgue integral being `⊤`. -/
theorem readingKoebe :
    koebe ∈ SSS ∧
    (∫⁻ w in DD, ENNReal.ofReal (‖deriv koebe w‖ ^ (-2 : ℝ)) = ⊤) ∧
    (∫⁻ w in DD, ENNReal.ofReal (‖deriv koebe w‖ ^ (2 / 3 : ℝ)) = ⊤) := by
  sorry

/-
AMBIGUITIES AND CHOICES
* Functions are `ℂ → ℂ`; only values on the relevant domain matter (DifferentiableOn / InjOn /
  BijOn on that domain; `deriv` is only evaluated at interior points of open sets, where
  differentiability on the open set gives differentiability at the point: no junk deriv).
* Univalent = DifferentiableOn ℂ + InjOn.  Univalent maps have nonvanishing derivative, so
  `‖f'‖ ^ t` for negative real `t` is an rpow of a positive base (no junk).  Same for a
  conformal bijection φ (derivative nonzero on W).
* Area measure: `volume` on `ℂ`, the Lebesgue measure.
* M_t: interval integral over [-π, π] of a continuous positive function on the circle of radius
  r<1 (f' continuous in the disk), so integrable, no junk.  r real, cast to ℂ.
* β_f: limsup in `EReal` along `𝓝[<] 1`, avoiding sSup/limsup in ℝ junk (the limsup may be ±∞
  in EReal in principle; that is a genuine value, not junk).  The quotient has M > 0 (positive
  integrand) so log is of a positive number, and log(1/(1-r)) > 0 for r ∈ (0,1) so no x/0
  eventually (the filter only sees r near 1).  Text's "equivalently infimum of b" not used.
* B_S: `⨆ f ∈ SSS, beta f t` in `EReal` (complete lattice; SSS is nonempty, e.g. Koebe).
  B_S(-2) = 1 stated as an EReal equality with `(1 : EReal)`.
* Uniform bound: `∃ C : ℝ` for each ε (C real, hence finite); `(1-r)^(-(1+ε))` is rpow with
  base 1-r ∈ (0,1/2], positive.
* "Simply connected plane domain": W open, `IsConnected W`, `SimplyConnectedSpace W`.
  "boundary in the Riemann sphere contains at least two points": image of W in `OnePoint ℂ`,
  `frontier` there, `encard ≥ 2` (encard is ℕ∞-valued, ⊤ for infinite sets is a genuine
  cardinality here, not a junk value).
* Conformal bijection φ : W → DD: `DifferentiableOn ℂ φ W` and `BijOn φ W DD`.  (Inverse is
  then automatically holomorphic.)
* Integrability: `IntegrableOn … volume` with Bochner integrability, so no `∫ = 0` junk.
  Range 4/3 < s < 4 and -2 < t < 2/3 as written.  The "equivalently" disk statement is a
  separate conjunct for every univalent f on DD (no normalization).
* Koebe: `z/(1-z)^2` on ℂ (value at z=1 irrelevant; division by zero junk occurs only off DD).
  For the integrals I use lintegral of `ENNReal.ofReal` of the nonnegative integrand; "= ∞" is
  `= ⊤`.  ⊤ is the intended value here (the divergence assertion), not a junk default.
  Koebe ∈ SSS is included in the corollary as the text says "belongs to".
-/

end ReaderB


/-!
Blind reading C, target O, family O64: Brennan's conjecture and sharp inverse-square integral means.
Definitions are written from the source excerpt; the claims are `sorry`.
See the comment block at the end for ambiguities and choices.
-/

namespace ReaderC

/-- The unit disk D. -/
def unitDisk : Set ℂ := Metric.ball 0 1

/-- The normalized schlicht class S: holomorphic, injective on D, f(0) = 0, f'(0) = 1. -/
def schlicht : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f unitDisk ∧ Set.InjOn f unitDisk ∧ f 0 = 0 ∧ deriv f 0 = 1}

/-- M_t[f'](r) = (1/2π) ∫_{−π}^{π} |f'(r e^{iθ})|^t dθ, with |·|^t the real power. -/
noncomputable def meanMt (f : ℂ → ℂ) (t r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    intervalIntegral
      (fun θ : ℝ => ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t)
      (-Real.pi) Real.pi MeasureTheory.volume

/-- β_f(t) = limsup_{r↑1} log M_t[f'](r) / log(1/(1−r)). -/
noncomputable def betaExp (f : ℂ → ℂ) (t : ℝ) : ℝ :=
  Filter.limsup (fun r : ℝ => Real.log (meanMt f t r) / Real.log (1 / (1 - r)))
    (nhdsWithin (1 : ℝ) (Set.Iio 1))

/-- B_S(t) = sup_{f ∈ S} β_f(t). -/
noncomputable def bigB (t : ℝ) : ℝ :=
  sSup ((fun f : ℂ → ℂ => betaExp f t) '' schlicht)

/-- The Koebe function z/(1 − z)², which lies in S (Corollary 1.2). -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- Theorem 1.1, all four assertions.
(i) uniform bound for M_{−2}, (ii) B_S(−2) = 1, (iii) the domain form for simply connected W
whose boundary in the Riemann sphere has at least two points, with conformal bijections
φ : W → D and exponents 4/3 < s < 4 (integrability: ∫_W |φ'|^s dA < ∞), and (iv) the disk form,
every univalent f : D → ℂ with −2 < t < 2/3 has ∫_D |f'|^t dA < ∞. -/
theorem reading_thm_1_1 :
    (∀ ε : ℝ, 0 < ε → ∃ Ceps : ℝ, ∀ f ∈ schlicht, ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
        meanMt f (-2) r ≤ Ceps * (1 - r) ^ (-1 - ε)) ∧
    bigB (-2) = 1 ∧
    (∀ W : Set ℂ, IsOpen W → IsConnected W → SimplyConnectedSpace ↥W →
        (∃ x y : OnePoint ℂ, x ∈ frontier (OnePoint.some '' W) ∧
            y ∈ frontier (OnePoint.some '' W) ∧ x ≠ y) →
        ∀ φ : ℂ → ℂ, Set.BijOn φ W unitDisk → DifferentiableOn ℂ φ W →
          ∀ s : ℝ, 4 / 3 < s → s < 4 →
            MeasureTheory.IntegrableOn (fun z : ℂ => ‖deriv φ z‖ ^ s) W MeasureTheory.volume) ∧
    (∀ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisk → Set.InjOn f unitDisk →
        ∀ t : ℝ, -2 < t → t < 2 / 3 →
          MeasureTheory.IntegrableOn (fun w : ℂ => ‖deriv f w‖ ^ t) unitDisk
            MeasureTheory.volume) :=
  sorry

/-- Corollary 1.2 (Koebe function): koebe ∈ S, and the integrals of |f'|^{−2} and |f'|^{2/3} over D
are infinite (stated as non-integrability). -/
theorem reading_cor_1_2 :
    koebe ∈ schlicht ∧
    ¬ MeasureTheory.IntegrableOn (fun z : ℂ => ‖deriv koebe z‖ ^ (-2 : ℝ)) unitDisk
        MeasureTheory.volume ∧
    ¬ MeasureTheory.IntegrableOn (fun z : ℂ => ‖deriv koebe z‖ ^ (2 / 3 : ℝ)) unitDisk
        MeasureTheory.volume :=
  sorry

end ReaderC

/-!
## Comment block: ambiguities and choices (reader C, O64)

1. Area measure. dA = dx dy is `MeasureTheory.volume` on ℂ (Mathlib identifies it with planar
   Lebesgue measure through ℂ ≃ ℝ × ℝ). Integrals ∫_W |φ'|^s dA < ∞ are stated as
   `IntegrableOn`, which for a nonnegative integrand is exactly "finite integral". The integrands
   are nonnegative, so no sign issue arises.

2. The normalized schlicht class. f : ℂ → ℂ is a function on the whole plane whose restriction to D
   matters: `DifferentiableOn ℂ f unitDisk` (holomorphic on D, an open set, so deriv is the complex
   derivative there), `Set.InjOn f unitDisk` (univalent), f 0 = 0, deriv f 0 = 1. Values outside D
   are irrelevant to every quantity below, since all integrals and M_t use only points in D.
   Univalence is used only on D.

3. M_t[f'](r). The formula (1/2π)∫_{−π}^{π}|f'(re^{iθ})|^t dθ is `intervalIntegral` with the
   Lebesgue measure, with r e^{iθ} written as (r : ℂ) * exp((θ:ℂ) * I). Junk values: for univalent f,
   f' has no zeros on D, so the base |f'| is positive and rpow is the honest power. The theorem's
   statements only ever use univalent f (schlicht or the disk form), so no junk arises there.
   The integrand is continuous on each circle, so the interval integral is the honest integral.

4. β_f(t). The text defines it as limsup_{r↑1} of log M_t / log(1/(1−r)). I use `Filter.limsup` along
   `nhdsWithin 1 (Iio 1)`. Real.log of M_t: M_t > 0 for univalent f (since f' ≠ 0), so the log is
   the honest one. Junk: if the limsup were unbounded, Lean's conditionally complete lattice would
   give a junk value; the uniform estimate in (i) bounds β_f(−2) ≤ 1 + ε for every ε (the log of
   C_ε(1−r)^{−1−ε} over log(1/(1−r)) tends to 1 + ε), so for t = −2 the values are bounded and no
   junk enters the statement (ii).

5. B_S(t) = sup_{f∈S} β_f(t). `bigB` is `sSup` of the image of `schlicht`. For t = −2 the set is
   nonempty (the Koebe function is in S) and bounded above by 1 (see 4), so the sSup is the honest
   supremum. The assertion B_S(−2) = 1 is therefore not satisfied vacuously by a junk 0.

6. Theorem 1.1 (i). "For every ε > 0 there is C_ε < ∞": `∀ ε, 0 < ε → ∃ Ceps : ℝ`, with the
   ordering (f, r) inside, as displayed. The condition 1/2 ≤ r < 1 is literal. The rpow (1 − r)^{−1−ε}
   has positive base since r < 1.

7. Theorem 1.1 (ii) is `bigB (-2) = 1`. The text's "B_S(-2) = 1" is taken literally.

8. Theorem 1.1 (iii), domain form. "Simply connected plane domain": W open and connected
   (`IsOpen W`, `IsConnected W`) and `SimplyConnectedSpace ↥W`. "Boundary in the Riemann sphere
   contains at least two points": frontier of the image of W in OnePoint ℂ (the Riemann sphere,
   with `OnePoint.some` the coercion ℂ → OnePoint ℂ), with two distinct points x ≠ y, avoiding
   Set.encard. "Conformal bijection φ : W → D": `Set.BijOn φ W unitDisk` and holomorphic on W
   (`DifferentiableOn ℂ φ W`). Conformal bijections are holomorphic bijections, and their derivatives
   are then automatically nonzero, so no separate condition is needed.

9. Theorem 1.1 (iv), disk form. Stated for every f : ℂ → ℂ holomorphic and injective on D, with
   −2 < t < 2/3, the integrability of |f'|^t on D. The text says "univalent map f : D → ℂ"; I take
   univalent to mean holomorphic and injective on D. The values of f outside D are not used.

10. Corollary 1.2. koebe z = z/(1 − z)² as a Lean function; at z = 1 Lean gives 1/0 = 0, but that
    point is not in D, so it does not affect anything. "∫ = ∞" is stated as non-integrability of the
    nonnegative integrand over D, which is the faithful version (Lean's ∫ is 0 on non-integrable
    functions, so a bare ∫ = ∞ cannot be written). Membership koebe ∈ S includes deriv koebe 0 = 1
    and koebe 0 = 0, with 0 ∈ D.

11. Not stated as separate claims: the text's remark that the inverse of the Koebe function fails
    area integrability at s = 4 and s = 4/3 (this is the domain-form negation of Corollary 1.2), and
    the statement that B_S(t) = |t| − 1 for t ≤ −2 (in the body of the text, not the theorem), which is
    not asked for. Omitted lines 92–end are not part of the excerpt.
-/
