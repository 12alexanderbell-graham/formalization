import Mathlib

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
