import Mathlib

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
