import Mathlib

/-- `A ⊆ [N] = {1..N}` has no two elements whose difference is a positive square
(difference 0 is not a square of m ≥ 1, so a = b is allowed). -/
def SqDiffFree (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → a ≠ b + m ^ 2

/-- Theorem 1.1, first part. -/
theorem reading_sqdiff_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, SqDiffFree N A →
      (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - c) := sorry

/-- "Equivalently": any subset of [N] larger than C N^{1-c} has distinct elements whose
absolute difference is a positive square. -/
theorem reading_sqdiff_equiv :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      C * (N : ℝ) ^ (1 - c) < (A.card : ℝ) →
        ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ m : ℕ, 1 ≤ m ∧ |(a : ℤ) - b| = (m : ℤ) ^ 2 := sorry

/- Ambiguities / choices:
* Differences in ℤ; I avoided ℕ subtraction by writing a = b + m^2 (ordered pair, both
  orders quantified) for freeness, and |(a:ℤ)-b| in the equivalent form.
* Constants c>0, C real (C<∞; C may be nonpositive but then bound only holds for empty A, still
  fine as an existential; the theorem is trivial-free since c can't exceed... c>1 would make
  the exponent negative: not excluded by source, but then the claim is stronger/false for
  A={1}; so truthfulness forces c<1 implicitly; I did not add it).
* N^(1-c) is rpow with positive base N ≥ 1, no junk. "Absolute constants" = independent of N, A.
* The two theorems each carry their own ∃ c C; the source's "equivalently" suggests the same
  constants, which the equivalence (contrapositive, a pure logical restatement) would give.
-/
