import Mathlib

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
