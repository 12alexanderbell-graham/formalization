import Mathlib

/-!
Blind reading A of O60, "Ordinary two-point correlations of multiplicative functions":
Theorem 1.1, Theorem 1.2, Corollary 1.3. Source: abstract + introduction lines 1-99.
-/

namespace ReaderA

open Filter Topology

/-- Liouville's function `λ(n) = (-1)^{Ω(n)}`, `Ω` = number of prime factors counted with
multiplicity (Mathlib's `ArithmeticFunction.cardFactors`). Only used at `n ≥ 1`. -/
noncomputable def liouville (n : ℕ) : ℝ := (-1 : ℝ) ^ (ArithmeticFunction.cardFactors n)

/-- Theorem 1.1. There is an absolute `c > 0` such that for all integers `a₁, a₂ ≥ 1`,
`b₁, b₂ ≥ 0` with `a₁b₂ - a₂b₁ ≠ 0` there is `C` with
`|∑_{1 ≤ n ≤ X} λ(a₁n+b₁) λ(a₂n+b₂)| ≤ C X / (log X)^c` for all real `X ≥ 3`. -/
theorem reading_thm_1_1 :
    ∃ c : ℝ, 0 < c ∧
      ∀ a₁ a₂ b₁ b₂ : ℕ, 1 ≤ a₁ → 1 ≤ a₂ → (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
        ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
          |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)|
            ≤ C * (X / Real.log X ^ c) := sorry

/-- `f : ℕ → 𝔻`: `|f(n)| ≤ 1` for every positive integer `n` (`ℕ` read as positive integers). -/
def DiscValued (f : ℕ → ℂ) : Prop := ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1

/-- Multiplicative as in the text: `f(mn) = f(m) f(n)` for coprime positive integers `m, n`
(no normalisation `f(1) = 1` is imposed, as the text imposes none). -/
def IsMultiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m * f n

/-- `D(f, χ n^{it}; X)^2 = ∑_{p ≤ X} (1 - Re(f(p) · conj(χ(p) p^{it}))) / p`, sum over primes
`p ≤ X`. Here `χ(p)` is `χ` evaluated at `p mod q`, and `p^{it} = exp(i t log p)` is the
complex power `(p : ℂ) ^ (t i)` with positive real base. -/
noncomputable def distSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊X⌋₊).filter Nat.Prime,
    (1 - (f p * starRingEnd ℂ (χ (p : ZMod q) * (p : ℂ) ^ ((t : ℂ) * Complex.I))).re) / (p : ℝ)

/-- The nonnegative distance `D(f, χ n^{it}; X)`, the nonnegative square root of `distSq`.
For `|f(p)| ≤ 1` every summand of `distSq` is `≥ 0` (since `|χ(p) p^{it}| ≤ 1`), so the
square root is of a nonnegative number (no `Real.sqrt` junk on the relevant class). -/
noncomputable def dist (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) : ℝ :=
  Real.sqrt (distSq f χ t X)

/-- Uniform nonpretentiousness (eq:unp): for every fixed Dirichlet character `χ` (of any
modulus `q ≥ 1`), `inf_{|t| ≤ N} D(f, χ n^{it}; N) → ∞` as `N → ∞` (real `N`).
The infimum tending to `∞` is written without `iInf`: for every `M` there is `N₀` such that
for all `N ≥ N₀` and all `|t| ≤ N`, `D(f, χ n^{it}; N) ≥ M`. -/
def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ χ : DirichletCharacter ℂ q, ∀ M : ℝ, ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
    ∀ t : ℝ, |t| ≤ N → M ≤ dist f χ t N

/-- Theorem 1.2 (binary corrected Elliott). -/
theorem reading_thm_1_2 (f₁ f₂ : ℕ → ℂ)
    (hf₁ : IsMultiplicative f₁) (hf₂ : IsMultiplicative f₂)
    (hd₁ : DiscValued f₁) (hd₂ : DiscValued f₂)
    (hunp : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (h₁ h₂ : ℕ) (hh : h₁ ≠ h₂) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂))
      atTop (𝓝 0) := sorry

/-- Corollary 1.3 (affine correlations). -/
theorem reading_cor_1_3 (f₁ f₂ : ℕ → ℂ)
    (hf₁ : IsMultiplicative f₁) (hf₂ : IsMultiplicative f₂)
    (hd₁ : DiscValued f₁) (hd₂ : DiscValued f₂)
    (hunp : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (hdet : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) :
    Tendsto (fun N : ℕ =>
        (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f₁ (a₁ * n + b₁) * f₂ (a₂ * n + b₂))
      atTop (𝓝 0) := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Integers vs naturals. `a₁,a₂ ≥ 1`, `b₁,b₂ ≥ 0`, `h₁,h₂ ≥ 0` are taken in `ℕ` (with the
   `≥ 1` conditions as hypotheses). The determinant `a₁b₂ - a₂b₁ ≠ 0` is computed in `ℤ`
   (casts), avoiding truncated ℕ subtraction.

2. Theorem 1.1 sum `∑_{1 ≤ n ≤ X}` for real `X`: `n ∈ Finset.Icc 1 ⌊X⌋₊` (`X ≥ 3 > 0`, so the
   floor is honest). `(log X)^c` is `Real.log X ^ c` (real power); `X ≥ 3` gives
   `log X > 0`, so no junk from `Real.log`/`rpow`/division. `C` is an arbitrary real
   (the text puts no sign constraint; it is necessarily ≥ 0 when the sum is nonzero).
   Quantifier order follows the text: `∃ c` before the forms, `∃ C` after them.
   `λ` is real-valued; arguments `a n + b ≥ 1`, so `Ω(0)` never enters.

3. `λ(n) = (-1)^{Ω(n)}` with `Ω = ArithmeticFunction.cardFactors` (Mathlib's Ω).

4. `ℕ` in `f : ℕ → 𝔻` read as positive integers (the text says multiplicativity is for
   coprime positive integers). Lean functions `ℕ → ℂ` have a value at 0 which is
   unconstrained and never used (all arguments `n + h`, `a n + b` with `n ≥ 1` are ≥ 1).
   `𝔻` constraint `|f(n)| ≤ 1` imposed only for `n ≥ 1`.

5. Multiplicative: exactly "f(mn) = f(m)f(n) for coprime positive m, n"; `f(1) = 1` is
   not required (it follows unless `f ≡ 0` on positive integers, a trivial case).

6. Dirichlet characters: Mathlib's `DirichletCharacter ℂ q` (= `MulChar (ZMod q) ℂ`) for
   every modulus `q ≥ 1`; `χ(p)` is `χ (p : ZMod q)` (so `χ(p) = 0` when `p ∣ q`, the
   usual convention). Modulus `q = 0` (ZMod 0 = ℤ) is excluded as not a Dirichlet
   character in the usual sense; including it would only add conditions that hold anyway.
   "For every fixed Dirichlet character" includes non-primitive characters.

7. `p^{it}` = `(p:ℂ) ^ (t * I)` (Mathlib cpow, base `p ≥ 2 > 0`, so equals `exp(i t log p)`).
   Overline = complex conjugation `starRingEnd ℂ`.

8. Distance: `D` is the nonnegative square root of the displayed sum (`Real.sqrt`). The sum
   is ≥ 0 for `|f(p)| ≤ 1` (each numerator is `1 - Re(w)` with `|w| ≤ 1`), so `Real.sqrt` is
   never applied to a negative number in the cases that matter. The text requires
   `X ≥ 2`; our `distSq` is defined for all real `X` (empty prime sum below 2), but it is
   only ever used for large `N`.

9. Uniform nonpretentiousness: the text's `N` is not declared integer or real; the
   displayed range `N → ∞` is read as real `N → ∞` (the distance was defined for real
   `X ≥ 2`, and `|t| ≤ N` is a real bound). Alternative: `N ∈ ℕ`; these differ slightly
   because the `t`-range grows continuously while the prime cutoff jumps. The prime cutoff
   and the height bound are both `N`, as the text stresses (line 73).
   `inf_{|t|≤N} D → ∞` is stated as `∀ M, ∃ N₀, ∀ N ≥ N₀, ∀ |t| ≤ N, D ≥ M`, which is
   exactly equivalent to the infimum (of a set of reals bounded below by 0, nonempty for
   `N ≥ 0`) tending to `+∞`, and avoids `iInf`/`sInf` junk.

10. Theorem 1.2 / Cor 1.3 averages: `(1/N) ∑_{n=1}^N ...` with `N ∈ ℕ`, `N → ∞`, written
   `(N : ℂ)⁻¹ * ∑ n ∈ Icc 1 N, ...` and `Tendsto … atTop (𝓝 0)`. At `N = 0`, `0⁻¹ = 0` is a
   junk value, but the limit along `atTop` does not depend on any finite set of `N`.
   "At least one satisfies (eq:unp)" = `UNP f₁ ∨ UNP f₂`. No conjugation in the product.
   Corollary 1.3 has no `N ∈ ℕ` stated explicitly; we use `N ∈ ℕ` as in Theorem 1.2.

11. Not formalized: the remarks after Theorem 1.1 (the special case `a₁=a₂=1`, residue-class
   versions) and Proposition "affine-progression" (outside the read lines); the brief asks
   only for 1.1, 1.2, 1.3.
-/
