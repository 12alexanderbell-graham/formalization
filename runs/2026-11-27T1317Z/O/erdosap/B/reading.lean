import Mathlib

namespace ReaderB

open scoped Classical

/-- `S ⊆ ℕ` contains a nonconstant `k`-term arithmetic progression `a, a+d, …, a+(k-1)d`, `d > 0`. -/
def HasAP (k : ℕ) (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ S

/-- `r_k(N)`: largest cardinality of a subset of `{1,…,N}` with no nonconstant `k`-AP
(max over a finite nonempty family: the empty set always qualifies). -/
noncomputable def r (k N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun S : Finset ℕ => ¬ HasAP k (S : Set ℕ))).sup Finset.card

/-- Theorem 1.1, density bound. -/
theorem readingDensityBound :
    ∀ k : ℕ, 3 ≤ k → ∃ C c ε : ℝ, 0 < C ∧ 0 < c ∧ 0 < ε ∧
      ∀ N : ℕ, 2 ≤ N → (r k N : ℝ) ≤ C * N * Real.exp (-c * (Real.log N) ^ ε) := sorry

/-- Theorem 1.1, "equivalently" threshold form. -/
theorem readingThreshold :
    ∀ k : ℕ, 3 ≤ k → ∃ A : ℝ, 1 ≤ A ∧
      ∀ (N : ℕ) (α : ℝ), 1 ≤ N → 0 < α → α ≤ 1 →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N → α * N ≤ (S.card : ℝ) →
          Real.log N ≥ A * (2 + Real.log (1 / α)) ^ A →
          HasAP k (S : Set ℕ) := sorry

/-- Corollary 1.2. -/
theorem readingReciprocal (A : Set ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hdiv : ¬ Summable (fun a : A => 1 / (a : ℝ))) :
    ∀ k : ℕ, HasAP k A := sorry

end ReaderB

/-
Ambiguities / choices.
* r_k(N): max of card over AP-free subsets of {1..N}, as Finset.sup over a filtered powerset (ℕ-valued);
  well-defined since ∅ is in the family, no sSup. Defined for all N, k (only used k ≥ 3, N ≥ 2).
* AP: a, d naturals, d > 0, all i < k: a + i*d ∈ S (no subtraction; elements of subsets of [N] are ℕ).
* Thm 1.1: constants C,c,ε real > 0 depending on k; log N is Real.log of a cast, N ≥ 2 so log N > 0
  (real power (log N)^ε via rpow is non-junk). Bound: r ≤ C * N * exp(-c * (log N)^ε).
* Threshold form: "α-dense subset of [N]" = card S ≥ α N, 0<α≤1; N ≥ 1 assumed (N=0 would make log 0 = 0
  junk; with N ≥ 1 hypotheses are vacuous at N=1). log(1/α) with α>0 is nonjunk, ≥ 0. A real, A ≥ 1,
  exponent real (rpow). Conclusion: nonconstant k-AP in S. (k ≥ 3 fixed as in source.)
* Corollary: A ⊆ ℕ; the source says "set of positive integers" in the intro, "A ⊆ ℕ" in the statement,
  so I assume all elements positive (otherwise 1/0 junk for a = 0). Divergence = ¬Summable of
  nonnegative terms (equivalent to sum = ∞). Conclusion for every length k (k = 0,1,2 trivially included),
  nonconstant means d > 0. Source's ℕ may be {1,2,...}; chose to require positivity as hypothesis.
-/
