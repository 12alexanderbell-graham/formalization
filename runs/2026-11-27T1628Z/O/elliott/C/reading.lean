import Mathlib

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
