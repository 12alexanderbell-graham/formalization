import Mathlib

open Real

/-- "no nonconstant k-term arithmetic progression": there are no a, d with d ≠ 0 such that
a, a+d, ..., a+(k-1)d all lie in S. (Progressions in ℕ; d > 0 WLOG, since reversing a
progression negates d.) -/
def NoNonconstantAP (k : ℕ) (S : Set ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ¬ (∀ i : ℕ, i < k → a + i * d ∈ S)

open Classical in
/-- "r_k(N) is the largest size of a subset of {1,…,N} with no nonconstant k-term arithmetic
progression." Well defined: the family is finite and contains ∅, so the sup is a genuine maximum. -/
noncomputable def r (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun S : Finset ℕ => NoNonconstantAP k (S : Set ℕ))).sup
    Finset.card

/-- Theorem 1.1: "For each fixed integer k≥3 there are constants C_k,c_k,ε_k>0 such that, for
every N≥2, r_k(N) ≤ C_k N exp(-c_k (log N)^{ε_k})." -/
theorem reading : ∀ k : ℕ, 3 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
    ∀ N : ℕ, 2 ≤ N →
      (r k N : ℝ) ≤ C * N * Real.exp (-c * (Real.log N) ^ ε) := by
  sorry

/-- Erdős problem 3: "If A ⊆ ℕ has Σ_{n∈A} 1/n = ∞ then must A contain arbitrarily long
arithmetic progressions?" (A a set of positive integers; divergence of a nonnegative series
means non-summability.) Answer: yes. -/
theorem reading_erdos : ∀ A : Set ℕ, (∀ n ∈ A, 0 < n) →
    ¬ Summable (fun n : A => (1 : ℝ) / (n : ℕ)) →
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A := by
  sorry

/-
Ambiguities / choices:
1. ℕ vs positive integers: Erdős says A ⊆ ℕ but 1/0 is undefined; I assume A consists of positive
   integers (hypothesis ∀ n ∈ A, 0 < n).
2. "Σ 1/n = ∞": encoded as ¬Summable (equivalent for nonnegative terms).
3. "Nonconstant" AP: common difference d ≠ 0; I use d > 0 in ℕ (equivalent up to reversal).
4. "Arbitrarily long APs": for every k there is a k-term AP in A (k = 0, 1 trivial; nonconstant d > 0).
5. r_k(N): defined as max over subsets of {1..N} (Finset.sup of cards over a finite nonempty family).
6. Constants: C, c, ε real, strictly positive, depending on k (quantifier order ∀k ∃C c ε ∀N≥2).
   log is natural log (any base only changes c); (log N)^ε is real rpow, log N > 0 for N ≥ 2.
7. Theorem 1.1 is stated for k ≥ 3 only; reading_erdos is for all k and is the stated consequence.
-/
