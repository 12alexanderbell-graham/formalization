import Mathlib

namespace EgyptianReading

/-- "`a/b = 1/n_1 + ... + 1/n_k, 2 ≤ n_1 < ... < n_k, n_i ∈ ℤ`": a length-`k` expansion of `a/b`
with strictly increasing denominators, all at least `2` (integers ≥ 2, so naturals). -/
def IsExpansion (a b k : ℕ) : Prop :=
  ∃ n : Fin k → ℕ, StrictMono n ∧ (∀ i, 2 ≤ n i) ∧
    ∑ i, (1 : ℚ) / (n i : ℚ) = (a : ℚ) / (b : ℚ)

/-- "The greedy algorithm shows that such expansions exist" (for `1 ≤ a < b`);
this nonemptiness is what makes `N` below meaningful. -/
theorem exists_expansion (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) : ∃ k, IsExpansion a b k := by
  sorry

/-- "`N(a,b)` be the least `k` for which `a/b = 1/n_1 + ... + 1/n_k`, `2 ≤ n_1 < ... < n_k`."
Defined as `sInf` of the set of admissible `k`; nonempty for `1 ≤ a < b` by `exists_expansion`.
The fraction `a/b` need not be in lowest terms (we use the rational `a/b` directly). -/
noncomputable def N2 (a b : ℕ) : ℕ := sInf {k : ℕ | IsExpansion a b k}

/-- "put `N(b) = max_{1 ≤ a < b} N(a,b)`". For `b ≥ 2` the index set `Ico 1 b` is nonempty,
so the `Finset.sup` (over ℕ) is a genuine maximum. -/
noncomputable def N (b : ℕ) : ℕ := (Finset.Ico 1 b).sup (fun a => N2 a b)

/-- Manuscript Theorem 1.1: "There are absolute constants `c₁, c₂ > 0` and `b₀` such that, for every
integer `b ≥ b₀`, `c₁ log log b ≤ N(b) ≤ c₂ log log b`." -/
theorem reading :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      c₁ * Real.log (Real.log b) ≤ (N b : ℝ) ∧ (N b : ℝ) ≤ c₂ * Real.log (Real.log b) := by
  sorry

/-- Erdős Problem 304: "Is it true that `N(b) ≪ log log b`?" answered affirmatively
(only the upper bound; differs from `reading`, which also has the lower bound). -/
theorem reading_erdos :
    ∃ C : ℝ, 0 < C ∧ ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      (N b : ℝ) ≤ C * Real.log (Real.log b) := by
  sorry

end EgyptianReading

/-
AMBIGUITIES
1. Integers n_i: "n_i ∈ ℤ" with n_i ≥ 2 forces naturals; I used ℕ with 2 ≤ n i.
2. Sum evaluated in ℚ; a/b not reduced (as the manuscript says), which is automatic in ℚ.
3. N(a,b) as sInf over ℕ; nonemptiness stated as `exists_expansion` (greedy), sorried.
4. N(b) as Finset.sup over Ico 1 b (max); for b ≤ 1 gives junk 0, irrelevant for b ≥ b0 ≥ 2
   (the theorem's b0 could be anything, but is existentially chosen, so large b is what matters).
5. "≪ log log b" read as: exists C>0, b0 with N(b) ≤ C log log b for all b ≥ b0 (asymptotic, for
   large b). Real.log (Real.log b) is positive for b ≥ 3.
6. Erdős question is only the upper bound, so reading_erdos differs from reading (reading implies it).
7. "k" could in principle be 0 only if a/b = 0, excluded since a ≥ 1.
-/
