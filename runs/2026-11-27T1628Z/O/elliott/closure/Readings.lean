import Mathlib

/-! # Target O, family elliott: the three blind readings of run 2026-11-27T1628Z (brief da5a1fc), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


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


open Filter Topology Complex

namespace ReaderB

/-- Liouville function λ(n) = (-1)^Ω(n), as a complex number. -/
noncomputable def liouville (n : ℕ) : ℂ := (-1 : ℂ) ^ (ArithmeticFunction.cardFactors n)

/-- Multiplicative f : ℕ → 𝔻 : modulus ≤ 1 and f(mn) = f(m) f(n) for coprime positive m, n. -/
def IsMultUnit (f : ℕ → ℂ) : Prop :=
  (∀ n, ‖f n‖ ≤ 1) ∧ ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m * f n

/-- D(f, χ n^{it}; X)^2 = ∑_{p ≤ X} (1 - Re(f(p) conj(χ(p)) p^{it})) / p. -/
noncomputable def distSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (X + 1)).filter Nat.Prime,
    (1 - (f p * (starRingEnd ℂ) (χ (p : ZMod q)) * (p : ℂ) ^ ((t : ℂ) * Complex.I)).re) / (p : ℝ)

/-- The distance D (nonnegative square root of a nonnegative sum). -/
noncomputable def dist' (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : ℝ :=
  Real.sqrt (distSq f χ t X)

/-- Uniformly nonpretentious: for every fixed Dirichlet character χ,
inf_{|t| ≤ N} D(f, χ n^{it}; N) → ∞. -/
def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    Tendsto (fun N : ℕ => ⨅ t : Set.Icc (-(N : ℝ)) (N : ℝ), dist' f χ t N) atTop atTop

/-- Theorem 1.1. -/
theorem readingThm1_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ, 1 ≤ a₁ → 1 ≤ a₂ →
      (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0 →
      ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
        ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)‖
          ≤ C * (X / Real.log X ^ c) := sorry

/-- Theorem 1.2 (binary corrected Elliott). -/
theorem readingThm1_2 (f₁ f₂ : ℕ → ℂ) (h₁ : IsMultUnit f₁) (h₂ : IsMultUnit f₂)
    (hunp : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (h₁' h₂' : ℕ) (hne : h₁' ≠ h₂') :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁') * f₂ (n + h₂'))
      atTop (𝓝 0) := sorry

/-- Corollary 1.3 (affine correlations). -/
theorem readingCor1_3 (f₁ f₂ : ℕ → ℂ) (h₁ : IsMultUnit f₁) (h₂ : IsMultUnit f₂)
    (hunp : UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂)
    (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 1 ≤ a₁) (ha₂ : 1 ≤ a₂)
    (hdet : (a₁ : ℤ) * b₂ - (a₂ : ℤ) * b₁ ≠ 0) :
    Tendsto (fun N : ℕ => (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, f₁ (a₁ * n + b₁) * f₂ (a₂ * n + b₂))
      atTop (𝓝 0) := sorry

/-
Ambiguities and choices.
* Ω(n): `ArithmeticFunction.cardFactors` (prime factors with multiplicity); λ(n) = (-1)^Ω(n) in ℂ.
* Thm 1.1: c absolute (quantified before the forms), C depends on (a₁,a₂,b₁,b₂) and is a real
  (no sign constraint needed). X real, ≥ 3, so log X > 0 and the real power X/(log X)^c is
  well defined (rpow with positive base, no junk). The sum is over 1 ≤ n ≤ X via ⌊X⌋₊.
  Nonvanishing a₁b₂ - a₂b₁ ≠ 0 is stated in ℤ (casts first), so no ℕ subtraction.
  a_i ≥ 1, b_i ≥ 0 as naturals; arguments a n + b ≥ 1 so λ is never evaluated at 0.
* Multiplicative: literal reading (coprime positive m,n). f(0) is unconstrained apart from
  |f(0)| ≤ 1 and never used in sums (arguments n+h ≥ 1). I do not require f 1 = 1
  (text doesn't; coprime case forces f 1 ∈ {0,1}). f : ℕ → 𝔻 encoded as ‖f n‖ ≤ 1.
* Dirichlet characters: `DirichletCharacter ℂ q` for every modulus q ≠ 0 (NeZero q);
  χ(p) = χ (p : ZMod q) (zero when gcd(p,q)>1). p^{it} = (p:ℂ)^(t*I) (complex cpow, p ≥ 2 so
  no 0^0 issue). Conjugation is `starRingEnd ℂ`.
* D: distSq is sum over primes p ≤ X of (1 - Re(...))/p; each summand is ≥ 0 since |f|≤1,
  |χ|≤1, |p^{it}|=1, so sqrt is of a nonnegative number. Division by p ≥ 2 never by zero.
  Cutoff X is a natural number N (the text uses real X ≥ 2 in general, but (eq:unp) only
  uses N → ∞ through naturals, so no loss). For N=0,1 the sum is empty (value 0); irrelevant
  for the limit.
* Uniform nonpretentiousness: iInf over the subtype Icc(-N,N) of reals, which is nonempty
  and bounded below by 0 (bounded, indeed a continuous function on a compact set, so the inf is a
  genuine min); no empty/unbounded inf. "Tends to ∞" is `Tendsto … atTop atTop` in ℝ.
  "Prime cutoff and the height bound are the same N" is respected.
* Thm 1.2: h₁ ≠ h₂ naturals (≥ 0). Average is (1/N)·sum with N:ℕ cast to ℂ; N = 0 gives the
  junk 1/0 = 0 but only affects one term, not the limit. Hypothesis "at least one satisfies
  (eq:unp)" is the disjunction. Limit is Tendsto atTop (𝓝 0).
* Cor 1.3: same, with the determinant condition in ℤ.
* Not formalized: Prop affine-progression, quantitative Liouville distance bound (not in the read
  text).
-/

end ReaderB


/-!
Reader C, family O60: ordinary two-point correlations of multiplicative functions.

Definitions are written from the text (abstract and introduction, lines 1-99).

Ambiguities and choices:
* Liouville `λ(n) = (-1)^{Ω(n)}`, with `Ω` counted with multiplicity, is
  `(-1)^(Nat.primeFactorsList n).length`. The statement only evaluates it at
  arguments `a n + b ≥ 1`, so `λ(0)` is never used.
* Admissible pairs: `a1, a2 ≥ 1` and `b1, b2 ≥ 0` are naturals, and the nonvanishing
  condition `a1 b2 - a2 b1 ≠ 0` is taken in `ℤ`, so there is no natural-number subtraction.
* Constants: Theorem 1.1 is stated as `∃ c > 0, ∀ admissible pair, ∃ C, ∀ X ≥ 3`, which
  matches "absolute c, constant C depending on the pair". `(log X) ^ c` is a real power
  of a positive quantity, since `log X > 0` for `X ≥ 3`.
* Cutoff `X` is real; the sum runs over `1 ≤ n ≤ ⌊X⌋₊`.
* Functions `f : ℕ → ℂ` with `‖f n‖ ≤ 1` for all `n` encode `f : ℕ → 𝔻`. The value at `0`
  is included in the disc condition, which is harmless because all uses have arguments `≥ 1`.
* Multiplicative: `f (m n) = f m f n` for coprime positive `m, n`.
* Distance: for `q ≥ 1` and `χ : DirichletCharacter ℂ q` (a `MulChar (ZMod q) ℂ`), `t, X : ℝ`,
  the squared distance is the sum over primes `p ≤ X` of `(1 - Re(f(p) conj(χ(p) p^{it}))) / p`.
  The text's `D` is its square root. `Real.sqrt` of a negative value would be junk, but the
  summand is nonnegative whenever `‖f p‖ ≤ 1` and `|χ(p)| = 1`, which holds for characters.
  Here `p^{it}` is `(p : ℂ) ^ (t * I)` with `p ≥ 1`, so there is no `0 ^ _` issue.
  Moduli `q` are restricted to `0 < q`, since `ZMod 0 = ℤ` is not a finite-modulus setting.
* Uniform nonpretentiousness: `inf_{|t|≤N} D(f, χ n^{it}; N) → ∞` as the real cutoff `N → ∞`.
  The infimum is `sInf` of the image of `Set.Icc (-N) N` under `t ↦ D`. This set is nonempty
  and bounded below by `0` for `N ≥ 0`, so `sInf` is the true infimum there. Only the
  behaviour as `N → ∞` matters, so the junk values for `N < 0` do not affect the statement.
* Theorem 1.2 uses `N : ℕ` with the normalisation `1/N` in `ℂ`. Division by `N = 0` is junk,
  but it does not matter for the limit.
* "At least one" of `f1`, `f2` is uniformly nonpretentious: encoded as a disjunction.
* Distinct nonnegative `h1 ≠ h2`, with `n + h` always `≥ 1` for `n ≥ 1`.
* Corollary 1.3 is stated with `a n + b` over `ℕ`, with `n ≥ 1`, so the argument is always `≥ 1`.
-/

namespace ReaderC

open Filter Topology

/-- Liouville function `λ(n) = (-1)^{Ω(n)}` with `Ω` counted with multiplicity. -/
def liouville (n : ℕ) : ℝ := (-1 : ℝ) ^ (Nat.primeFactorsList n).length

/-- Multiplicative function on positive integers, with `f (m n) = f m f n` for coprime `m, n ≥ 1`. -/
def IsMultiplicativeFn (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → f (m * n) = f m * f n

/-- Values in the closed unit disc `𝔻 = {z : |z| ≤ 1}`. -/
def InUnitDisc (f : ℕ → ℂ) : Prop := ∀ n : ℕ, ‖f n‖ ≤ 1

/-- Squared distance `D(f, χ n^{it}; X)^2`, summing over primes `p ≤ X`. -/
noncomputable def distSq {q : ℕ} (f : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
    (1 - (f p * (starRingEnd ℂ) (χ (p : ZMod q) * (p : ℂ) ^ ((t : ℂ) * Complex.I))).re) / (p : ℝ)

/-- Distance `D(f, χ n^{it}; X)`, the square root of `distSq`. -/
noncomputable def dist' {q : ℕ} (f : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t X : ℝ) : ℝ :=
  Real.sqrt (distSq f χ t X)

/-- Uniform nonpretentiousness: for every modulus `q ≥ 1` and every Dirichlet character `χ`
modulo `q`, `inf_{|t| ≤ N} D(f, χ n^{it}; N) → ∞` as `N → ∞`. -/
def IsUnifNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ χ : DirichletCharacter ℂ q,
    Tendsto (fun N : ℝ => sInf ((fun t => dist' f χ t N) '' Set.Icc (-N) N)) atTop atTop

/-- Reading of Theorem 1.1: absolute `c > 0` and the Liouville bound for every admissible pair. -/
theorem reading_liouville_affine_saving :
    ∃ c : ℝ, 0 < c ∧
      ∀ a1 a2 b1 b2 : ℕ, 1 ≤ a1 → 1 ≤ a2 → (a1 : ℤ) * b2 - (a2 : ℤ) * b1 ≠ 0 →
        ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
          |∑ n ∈ Finset.Icc 1 ⌊X⌋₊, liouville (a1 * n + b1) * liouville (a2 * n + b2)|
            ≤ C * X / (Real.log X) ^ c := by
  sorry

/-- Reading of Theorem 1.2: binary corrected Elliott for ordinary averages. -/
theorem reading_binary_corrected_elliott :
    ∀ f1 f2 : ℕ → ℂ, InUnitDisc f1 → InUnitDisc f2 →
      IsMultiplicativeFn f1 → IsMultiplicativeFn f2 →
      (IsUnifNonpretentious f1 ∨ IsUnifNonpretentious f2) →
      ∀ h1 h2 : ℕ, h1 ≠ h2 →
        Tendsto (fun N : ℕ =>
          (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, f1 (n + h1) * f2 (n + h2))
          atTop (𝓝 0) := by
  sorry

/-- Reading of Corollary 1.3: affine correlations. -/
theorem reading_affine_correlations :
    ∀ f1 f2 : ℕ → ℂ, InUnitDisc f1 → InUnitDisc f2 →
      IsMultiplicativeFn f1 → IsMultiplicativeFn f2 →
      (IsUnifNonpretentious f1 ∨ IsUnifNonpretentious f2) →
      ∀ a1 a2 b1 b2 : ℕ, 1 ≤ a1 → 1 ≤ a2 → (a1 : ℤ) * b2 - (a2 : ℤ) * b1 ≠ 0 →
        Tendsto (fun N : ℕ =>
          (1 / (N : ℂ)) * ∑ n ∈ Finset.Icc 1 N, f1 (a1 * n + b1) * f2 (a2 * n + b2))
          atTop (𝓝 0) := by
  sorry

end ReaderC
