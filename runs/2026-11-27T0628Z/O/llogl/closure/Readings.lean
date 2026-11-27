import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

open MeasureTheory Filter Topology

namespace ReaderB

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- 𝕋 = ℝ/(2πℤ). -/
abbrev T : Type := AddCircle (2 * Real.pi)

/-- Normalized Lebesgue measure dμ = dx/(2π) (Mathlib's `volume` on `AddCircle (2π)` has mass 2π). -/
noncomputable def μ : Measure T := ENNReal.ofReal (1 / (2 * Real.pi)) • (volume : Measure T)

/-- e^{ikx} on 𝕋. Mathlib's `fourier k x = exp(2πi k x / (2π)) = exp(i k x)`. -/
noncomputable def e (k : ℤ) (x : T) : ℂ := fourier k x

/-- \hat f(k) = ∫ f(x) e^{-ikx} dμ(x). -/
noncomputable def fhat (f : T → ℂ) (k : ℤ) : ℂ := ∫ x, f x * e (-k) x ∂μ

/-- S_N f(x) = ∑_{k=-N}^{N} \hat f(k) e^{ikx}. -/
noncomputable def S (N : ℕ) (f : T → ℂ) (x : T) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) N, fhat f k * e k x

/-- f ∈ L log L: f measurable and ∫ |f| log(2+|f|) dμ < ∞. -/
def InLLogL (f : T → ℂ) : Prop :=
  AEStronglyMeasurable f μ ∧
    ∫⁻ x, ENNReal.ofReal (‖f x‖ * Real.log (2 + ‖f x‖)) ∂μ < ⊤

theorem reading_thm_1_1 (f : T → ℂ) (hf : InLLogL f) :
    ∃ Nf : Set T, MeasurableSet Nf ∧ μ Nf = 0 ∧
      ∀ x ∈ Nfᶜ, Tendsto (fun N : ℕ => S N f x) atTop (𝓝 (f x)) := sorry

end ReaderB

/-
Ambiguities / choices
- 𝕋 := AddCircle (2π); μ := (1/(2π)) • volume, a probability measure (volume has mass 2π).
- e^{ikx} realised as Mathlib's `fourier k x`; with period 2π this is exp(i k x). Not proved here.
- f is a genuine function T → ℂ (not an a.e. class). L log L membership: AEStronglyMeasurable
  plus finite lintegral of ofReal(|f| log(2+|f|)). Integrand is nonnegative so ofReal loses nothing.
- Junk values: the Bochner integral defining f̂ is 0 for non-integrable f; but L log L ⊂ L¹ (|f| ≤ C + |f|log(2+|f|)),
  so under the hypothesis f is integrable and f̂ is the true coefficient. No integrability hypothesis added.
- Conclusion: exists measurable null set Nf with convergence off Nf, full sequence N = 0,1,2,... (N : ℕ, atTop).
  Pointwise value f x is the one of the chosen representative; modifying f on a null set changes only Nf.
- Sum over k ∈ Icc (-N) N in ℤ, symmetric.
-/

-- ===== reader C =====

/-!
Reading of O17 (llogl), from `introduction_lines1-27.tex` only.
-/

open MeasureTheory Filter Topology Finset
open scoped Real

namespace ReaderC

namespace LLogL

/-- The circle `𝕋 = ℝ/(2πℤ)`, as in the source. -/
abbrev T := AddCircle (2 * π)

/-- The source's `𝕋` has `2π` as period, so `0 < 2π` is needed by Mathlib's `AddCircle`. -/
instance factTwoPiPos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Normalised Lebesgue measure `dμ = dx/(2π)`, i.e. Haar measure of total mass 1. -/
noncomputable abbrev μ : Measure T := AddCircle.haarAddCircle

/-- Fourier coefficient `f̂(k) = ∫_𝕋 f(x) e^{-ikx} dμ(x)`.
Mathlib's `fourier n x = exp(2π i n x / T)` with `T = 2π` gives `exp(i n x)` for a real
representative `x`, so `e^{-ikx}` is `fourier (-k)`. -/
noncomputable def fhat (f : T → ℂ) (k : ℤ) : ℂ :=
  ∫ x, f x * fourier (-k) x ∂μ

/-- Symmetric partial sums `S_N f(x) = Σ_{k=-N}^{N} f̂(k) e^{ikx}`. -/
noncomputable def S (N : ℕ) (f : T → ℂ) (x : T) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fhat f k * fourier k x

/-- Membership in `L log L(𝕋)`: `f` is measurable and `∫ |f| log(2 + |f|) dμ < ∞`.
The integral is taken as a lower Lebesgue integral of a nonnegative function, so no
Bochner-integral junk value can appear. -/
def InLLogL (f : T → ℂ) : Prop :=
  AEStronglyMeasurable f μ ∧
    ∫⁻ x, ENNReal.ofReal (‖f x‖ * Real.log (2 + ‖f x‖)) ∂μ < ⊤

/-- Theorem 1.1 (reading): every complex `f ∈ L log L(𝕋)` has `S_N f → f` a.e.,
along the full sequence `N = 0, 1, 2, …`, with an exceptional set `N_f` that is measurable
and of measure zero. -/
theorem reading_llogl_ae_convergence (f : T → ℂ) (hf : InLLogL f) :
    ∃ Nf : Set T, MeasurableSet Nf ∧ μ Nf = 0 ∧
      ∀ x ∉ Nf, Tendsto (fun N : ℕ => S N f x) atTop (𝓝 (f x)) := by
  sorry

end LLogL

end ReaderC

/-!
Ambiguities and choices (O17, llogl):

1. Circle and measure. `𝕋 = ℝ/(2πℤ)` is modelled as `AddCircle (2π)`. `dμ = dx/(2π)` is
   Mathlib's `haarAddCircle`, which is the Haar measure normalised to total mass 1. This matches
   the source's normalised Lebesgue measure. I checked this against Mathlib's source
   (`Mathlib/Analysis/Fourier/AddCircle.lean`, `haarAddCircle` has `IsProbabilityMeasure`).
2. Exponential. The source writes `e^{-ikx}` with `x` real. I used Mathlib's `fourier n`, which
   at `T = 2π` is `exp(2π i n x / (2π)) = exp(i n x)`. So `e^{-ikx}` is `fourier (-k)`.
3. Partial sums. `S_N` uses `Finset.Icc (-N) N` over `ℤ`, which is the source's symmetric range
   `k = -N, …, N`.
4. The "complex-valued f" is a genuine function `T → ℂ`. The source only needs `f` to be
   measurable and in `L log L`. The `AEStronglyMeasurable f μ` clause is my addition to make
   the integral meaningful. The source does not mention measurability.
5. `L log L` uses the source's `log(2+|f|)` inside a lower integral `∫⁻` of `ENNReal.ofReal`
   of the nonnegative integrand. This avoids Bochner-integral junk for non-integrable `f`.
   Since `log(2+t) ≥ log 2 > 0`, membership forces `f ∈ L¹`, so `fhat f k` is a genuine integral
   for every `f` satisfying `InLLogL`. This is a consequence, not an extra hypothesis.
6. Exceptional set. The source says "a measurable set `N_f` of measure zero". I used
   `MeasurableSet Nf ∧ μ Nf = 0`, and the convergence is stated pointwise on `T \ N_f`.
7. The limit is along `N : ℕ` in `atTop`, as the source says "the full sequence N=0,1,2,…".
   The sum uses `N : ℕ` cast to `ℤ` for the index range.
8. No junk values were introduced for the headline. The theorem is `sorry` as required.
-/
