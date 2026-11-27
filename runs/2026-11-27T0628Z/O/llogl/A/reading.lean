import Mathlib

namespace ReaderA

open MeasureTheory Filter Topology Real

noncomputable section

/-- `0 < 2π`, needed to build the measure space structure on `ℝ/(2πℤ)`. -/
instance twoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The source's torus `𝕋 = ℝ/(2πℤ)`. `AddCircle (2*π)` is by definition `ℝ ⧸ zmultiples (2*π)`. -/
abbrev Torus : Type := AddCircle (2 * π)

/-- The source's normalized Lebesgue measure `dμ(x) = dx/(2π)`.
Mathlib's `volume` on `AddCircle (2π)` is Lebesgue measure transported from a fundamental
interval (total mass `2π`); we divide it by `2π`. -/
def μ : Measure Torus := (ENNReal.ofReal (2 * π))⁻¹ • (volume : Measure Torus)

/-- `t ↦ e^{ikt}` is `2π`-periodic on `ℝ`. -/
theorem expChar_periodic (k : ℤ) :
    Function.Periodic (fun t : ℝ => Complex.exp (Complex.I * (k : ℂ) * (t : ℂ))) (2 * π) := by
  intro t
  have h : Complex.I * (k : ℂ) * (((t + 2 * π : ℝ)) : ℂ)
      = Complex.I * (k : ℂ) * (t : ℂ) + (k : ℂ) * (2 * (π : ℂ) * Complex.I) := by
    push_cast; ring
  simp only
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The function `x ↦ e^{ikx}` on `𝕋`, obtained by descending the `2π`-periodic function
`t ↦ e^{ikt}` on `ℝ` to the quotient. -/
def expChar (k : ℤ) (x : Torus) : ℂ := (expChar_periodic k).lift x

/-- The source's Fourier coefficient `f̂(k) = ∫_𝕋 f(x) e^{-ikx} dμ(x)`. -/
def fourierCoeffT (f : Torus → ℂ) (k : ℤ) : ℂ :=
  ∫ x, f x * expChar (-k) x ∂μ

/-- The source's symmetric partial sum `S_N f(x) = ∑_{k=-N}^{N} f̂(k) e^{ikx}`. -/
def partialSum (N : ℕ) (f : Torus → ℂ) (x : Torus) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeffT f k * expChar k x

/-- The Orlicz class `L log L(𝕋) = {f : ∫_𝕋 |f(x)| log(2 + |f(x)|) dμ(x) < ∞}`.
Membership is stated with the (extended, nonnegative) lower Lebesgue integral, so that
"`< ∞`" is meaningful and not a junk value of the Bochner integral; `f` is required to be
(a.e. strongly) measurable, which the source leaves implicit. -/
def LlogL (f : Torus → ℂ) : Prop :=
  AEStronglyMeasurable f μ ∧
    ∫⁻ x, ENNReal.ofReal (‖f x‖ * Real.log (2 + ‖f x‖)) ∂μ < ⊤

/-- Theorem 1.1 (Almost-everywhere convergence in `L log L`). For every complex-valued
`f ∈ L log L(𝕋)` there is a measurable set `N_f` of measure zero such that
`S_N f(x) → f(x)` along the full sequence `N = 0, 1, 2, …` for every `x ∈ 𝕋 \ N_f`. -/
theorem reading_thm_1_1 (f : Torus → ℂ) (hf : LlogL f) :
    ∃ Nf : Set Torus, MeasurableSet Nf ∧ μ Nf = 0 ∧
      ∀ x ∈ (Set.univ \ Nf),
        Tendsto (fun N : ℕ => partialSum N f x) atTop (𝓝 (f x)) := sorry

end

end ReaderA

/-
Ambiguities and choices (Reader A, O17 llogl):

1. 𝕋 = ℝ/(2πℤ): taken literally as `AddCircle (2*π)`, i.e. `ℝ ⧸ AddSubgroup.zmultiples (2*π)`.
   A `Fact (0 < 2*π)` instance is declared by me (Mathlib only has a local one) to get the
   measure-space structure.

2. μ = dx/(2π): Mathlib's `volume` on `AddCircle T` is the Haar measure of total mass `T`
   (the pushforward of Lebesgue measure on a fundamental interval [a, a+T)); I define
   μ := (ofReal (2π))⁻¹ • volume, a probability measure. This should coincide with
   `AddCircle.haarAddCircle`, but I wrote the source's formula instead of using it.

3. e^{ikx} for x ∈ 𝕋: x is a coset, so e^{ikx} is defined by descending the 2π-periodic
   function t ↦ exp(i k t) on ℝ to the quotient (`Function.Periodic.lift`). Periodicity is
   proved (no sorry). e^{-ikx} is `expChar (-k)`.

4. f̂(k): the source defines it "for an integrable f"; in Lean I use the Bochner integral
   `∫ x, f x * e^{-ikx} ∂μ`, which would be a junk 0 for non-integrable f. Junk is avoided in
   the theorem because f ∈ L log L implies f integrable w.r.t. μ (μ is finite, f measurable
   and |f| ≤ |f| log(2+|f|)/log 2 since log(2+|f|) ≥ log 2 > 0); I did not add `Integrable f μ`
   as a separate hypothesis since it is a consequence, and adding it would not change the claim.

5. L log L: the integral is written as a lower Lebesgue integral (`∫⁻`) of the nonnegative
   function |f| log(2+|f|), so "< ∞" is genuinely the finiteness condition (a Bochner integral
   would be 0 when non-integrable, which would make every measurable f "belong"). The source's
   set-builder leaves measurability of f implicit; I require `AEStronglyMeasurable f μ`.
   (Using `AEStronglyMeasurable` rather than `StronglyMeasurable` is harmless: the conclusion
   is an a.e. statement modulo a null set; a stronger measurability hypothesis would only
   weaken the theorem.)

6. f is a genuine function 𝕋 → ℂ (not an L¹ class); the theorem is stated for every
   representative, which matches "lim S_N f(x) = f(x) for x ∉ N_f" literally (S_N f does not
   depend on the representative).

7. "measurable set N_f of measure zero": `MeasurableSet Nf ∧ μ Nf = 0` (measure zero for μ,
   equivalently for Lebesgue measure). `𝕋 \ N_f` is written `Set.univ \ Nf`.

8. "lim_{N→∞} along the full sequence N = 0,1,2,…": `Tendsto (fun N : ℕ => S_N f x) atTop
   (𝓝 (f x))` with N : ℕ, i.e. the full sequence of symmetric partial sums (not a subsequence,
   not lacunary).
-/
