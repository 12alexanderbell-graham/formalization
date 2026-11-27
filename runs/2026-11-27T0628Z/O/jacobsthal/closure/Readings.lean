import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

open Real

/-- `m` has the Jacobsthal property for `n`: every interval of `m` consecutive integers
`{a, a+1, …, a+m-1}` (`a ∈ ℤ` arbitrary) contains an integer coprime to `n`. -/
def JacProp (n m : ℕ) : Prop :=
  ∀ a : ℤ, ∃ x : ℤ, a ≤ x ∧ x < a + m ∧ IsCoprime x (n : ℤ)

/-- Jacobsthal's function `j(n)`: the least positive integer `m` with `JacProp n m`. -/
noncomputable def j (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ JacProp n m}

/-- Sanity lemma (proved): for `n ≥ 1` the set in the definition of `j n` is nonempty
(`m = n` works), so `sInf` is not the junk value `0` of the empty set. -/
theorem jac_set_nonempty (n : ℕ) (hn : 1 ≤ n) : n ∈ {m : ℕ | 0 < m ∧ JacProp n m} := by
  refine ⟨hn, fun a => ?_⟩
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨a + (1 - a) % (n : ℤ), ?_, ?_, ?_⟩
  · have := Int.emod_nonneg (1 - a) hn'
    omega
  · have := Int.emod_lt_of_pos (1 - a) (by exact_mod_cast hn : (0 : ℤ) < n)
    omega
  · refine ⟨1, (1 - a) / (n : ℤ), ?_⟩
    rw [Int.emod_def]
    ring

/-- `ω(n)`: the number of distinct prime divisors of `n` (so `ω(1) = 0`). -/
def ω (n : ℕ) : ℕ := n.primeFactors.card

/-- `h(k) = sup_{n ≥ 1, ω(n) ≤ k} j(n)`, taken in `ℕ∞` (embedded in `ℝ≥0∞`) so that an
unbounded family gives `⊤` rather than a junk value. -/
noncomputable def h (k : ℕ) : ENNReal :=
  ⨆ (n : ℕ) (_ : 1 ≤ n ∧ ω n ≤ k), ((j n : ℕ) : ENNReal)

/-- Theorem 1.1: there is an absolute `C > 0` with
`h(k) ≤ C k² / (log log (3k))²` for every integer `k ≥ 1`. -/
theorem reading_thm_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      h k ≤ ENNReal.ofReal (C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2) := by
  sorry

/-- Jacobsthal's question (answered affirmatively by Theorem 1.1): `h(k) ≪ k²`, i.e.
there is `C > 0` with `h(k) ≤ C k²` for every `k ≥ 1`. -/
theorem reading_jacobsthal_question :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → h k ≤ ENNReal.ofReal (C * (k : ℝ) ^ 2) := by
  sorry

end ReaderA

/-
Ambiguities and choices.

1. "interval of m consecutive integers": the set {a, …, a+m-1} with arbitrary start a ∈ ℤ
   (the text stresses the starting point is arbitrary), written as a ≤ x ∧ x < a + m in ℤ,
   so there is no ℕ subtraction.
2. "coprime to n": IsCoprime x (n : ℤ) in ℤ, which is equivalent to gcd(x, n) = 1
   (Int.isCoprime_iff_gcd_eq_one).
3. j(n) "least positive integer m": sInf of {m | 0 < m ∧ JacProp n m}. The empty set would
   give the junk value 0; this is excluded for n ≥ 1 by the proved lemma jac_set_nonempty
   (m = n works). j is only used at n ≥ 1, as in the source ("for a positive integer n").
4. ω(n) = card of n.primeFactors, written directly (ω(1) = 0 holds since primeFactors 1 = ∅).
   I did not use Mathlib's ArithmeticFunction.cardDistinctFactors, to write the definition
   myself; it agrees with it.
5. h(k) as a sup: taken in ENNReal (ℝ≥0∞) via iSup, so that if the family were unbounded
   the sup is ⊤ (and the theorems would then be false), not a junk `sSup` value of ℕ or ℝ.
   The range n ≥ 1, ω(n) ≤ k is the source's; h is only claimed for k ≥ 1.
6. The real bound is compared via ENNReal.ofReal. For k ≥ 1, log(3k) ≥ log 3 > 1, so
   log log(3k) > 0 and its square is positive: no division by 0 and no log of a small
   argument producing junk. "All logarithms are natural": Real.log.
7. "h(k) ≪ k²" (Jacobsthal's question): read as ∃ C > 0, ∀ k ≥ 1, h(k) ≤ C k² (Vinogradov
   notation over the stated domain k ≥ 1). The alternative "for all sufficiently large k"
   differs only if some h(k) were ⊤ (h is nondecreasing); I chose the uniform form, which is
   what Theorem 1.1 directly implies.
8. The constant C is "absolute": a single existential ∃ C quantified before k.
-/

-- ===== reader B =====

open scoped ENNReal
namespace ReaderB

/-- `m` consecutive integers starting at any `a` always contain one coprime to `n`. -/
def Good (n m : ℕ) : Prop := ∀ a : ℤ, ∃ i : ℕ, i < m ∧ IsCoprime (a + i) (n : ℤ)

/-- `j n`: least positive `m` with `Good n m` (for `n ≥ 1` the set is nonempty: `m = n` works). -/
noncomputable def j (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ Good n m}

/-- `ω n`: number of distinct prime divisors (`ω 1 = 0`). -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- `h k = sup_{n ≥ 1, ω n ≤ k} j n`, as a supremum in `ℕ∞` so an unbounded family gives `⊤`, not `0`. -/
noncomputable def h (k : ℕ) : ℕ∞ := ⨆ n : {n : ℕ // 1 ≤ n ∧ omega n ≤ k}, (j n.1 : ℕ∞)

/-- Theorem 1.1. -/
theorem reading_jacobsthal_main :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      ((h k : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * k))) ^ 2) := sorry

/-- Jacobsthal's question `h(k) ≪ k²` (weaker consequence). -/
theorem reading_jacobsthal_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ((h k : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (C * (k : ℝ) ^ 2) := sorry

/-
Ambiguities / choices:
* j(n) uses natural-number sInf over a set that is nonempty for n ≥ 1 (m = n), so no junk; for n = 0 it
  is never used because h ranges over n ≥ 1. "Coprime to n" is IsCoprime in ℤ (equiv. to gcd = 1).
  Interval start a ranges over all integers (source: starting point arbitrary).
* h is an iSup in ℕ∞ (complete lattice), so unboundedness would give ⊤ and the bound would then fail;
  no sSup-of-unbounded junk 0. Comparison is made in ℝ≥0∞ via ofReal, so the real RHS needs no toReal.
* log log (3k): for k ≥ 1, 3k ≥ 3 > e, so log(3k) > 1 and log log(3k) > 0: no junk log. Natural log.
* "ω(n) ≤ k" with k ≥ 1 as in the source.
* ofReal truncates negatives, but RHS is positive.
-/
end ReaderB

-- ===== reader C =====

namespace ReaderC

/-- j(n) for n ≥ 1: the least positive m such that every interval of m consecutive
integers {a, a+1, …, a+m-1} contains an integer coprime to n.
Valued in ℕ∞; the infimum over an empty index set is ⊤ (never 0), so no junk value. -/
noncomputable def jac (n : ℕ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : 0 < m ∧ ∀ a : ℤ, ∃ i : ℕ, i < m ∧ Int.gcd (a + (i : ℤ)) (n : ℤ) = 1),
    (m : ℕ∞)

/-- h(k) = sup { j(n) : n ≥ 1, ω(n) ≤ k }, with ω(n) = #(distinct prime divisors of n).
Valued in ℕ∞; a supremum over an unbounded set is ⊤, never a finite junk value. -/
noncomputable def hJac (k : ℕ) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : 1 ≤ n ∧ n.primeFactors.card ≤ k), jac n

/-- Theorem 1.1: there is an absolute C > 0 with h(k) ≤ C k² / (log log (3k))² for all k ≥ 1.
The right side is a real number; we compare in ℝ≥0∞ through `ENat.toENNReal`. -/
theorem reading_jacobsthal_main :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      ENat.toENNReal (hJac k) ≤
        ENNReal.ofReal (C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2) := sorry

/-- The weaker statement the text says it answers: Jacobsthal's question (recorded by Erdős)
whether h(k) ≪ k², i.e. h(k) ≤ C k² for all k ≥ 1 with some absolute C > 0. -/
theorem reading_jacobsthal_erdos_question :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k →
      ENat.toENNReal (hJac k) ≤ ENNReal.ofReal (C * (k : ℝ) ^ 2) := sorry

/-
Ambiguities and choices (reader C):

1. j(n) is defined for n ≥ 1 only; the theorems quantify over n ≥ 1 in hJac, so n = 0
   never enters (ω(0) would be junk in Mathlib's primeFactors).
2. "least positive integer m": the set of admissible m is nonempty (classical: Jacobsthal's
   function is finite), but I did not prove or need that; if it were empty the
   infimum is ⊤, not 0. The `0 < m` guard is kept literally although it is implied.
3. "Interval of m consecutive integers" is read as {a, …, a+m-1} for a ∈ ℤ, and
   "contains an integer coprime to n" as ∃ i < m with gcd(a+i, n) = 1 (Int.gcd).
4. ω(n) is `n.primeFactors.card` (distinct primes); ω(1) = 0 holds automatically.
5. h(k) is a supremum in ℕ∞ (iSup). The text's sup is over an index set that the
   theorem shows is bounded in ℝ-growth; in ℕ∞ an unbounded sup is ⊤ rather than a
   junk finite value. The reading theorems compare via ENat.toENNReal into ℝ≥0∞, so
   ⊤ is a genuine failure of the bound and not hidden.
6. The bound's right side uses natural logarithms (the text says "All logarithms are
   natural"). For k ≥ 1, log(3k) ≥ log 3 > 1, so log log(3k) > 0 and the division is
   well defined; the bound is written as ENNReal.ofReal of a positive real.
7. Theorem 1.1 asserts existence of an absolute C > 0 (not a specified value), as in the text.
8. The second theorem is the Erdős/Jacobsthal question h(k) ≪ k² (absolute constant C > 0,
   all k ≥ 1). It is stated separately as the text says Theorem 1.1 answers it; it is not
   derived here.
-/

end ReaderC
