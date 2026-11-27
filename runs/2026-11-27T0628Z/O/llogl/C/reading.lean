import Mathlib

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
