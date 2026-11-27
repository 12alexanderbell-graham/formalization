import Mathlib

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
