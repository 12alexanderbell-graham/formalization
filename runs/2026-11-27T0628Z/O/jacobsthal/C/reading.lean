import Mathlib

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
