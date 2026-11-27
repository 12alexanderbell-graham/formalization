import Mathlib

namespace ReaderB

open Finset

/-- Signed prefix sums bound: signs `ε : Fin N → ℝ` with values ±1, all prefixes `k ≤ N`
(prefix `k` = indices with `i.val < k`) have norm at most `C √d`. -/
def SigningBound (C : ℝ) : Prop :=
  ∀ d N : ℕ, 1 ≤ d → 1 ≤ N → ∀ v : Fin N → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ ≤ 1) →
    ∃ ε : Fin N → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ k : ℕ, k ≤ N →
        ‖∑ i ∈ univ.filter (fun i : Fin N => i.val < k), ε i • v i‖ ≤ C * Real.sqrt d

/-- Reordering bound: for zero-sum families of unit-ball vectors some permutation has all
prefix sums of norm at most `C √d`. -/
def SteinitzBound (C : ℝ) : Prop :=
  ∀ d N : ℕ, 1 ≤ d → 1 ≤ N → ∀ v : Fin N → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ ≤ 1) →
    ∑ i, v i = 0 →
    ∃ π : Equiv.Perm (Fin N),
      ∀ k : ℕ, k ≤ N →
        ‖∑ i ∈ univ.filter (fun i : Fin N => i.val < k), v (π i)‖ ≤ C * Real.sqrt d

/-- Theorem 1.1. -/
theorem readingSigning : ∃ C : ℝ, SigningBound C := sorry

/-- Theorem 1.2. -/
theorem readingSteinitz : ∃ C : ℝ, SteinitzBound C := sorry

/-- Theorem 1.2 with the final sentence: one constant works for both. -/
theorem readingSameConstant : ∃ C : ℝ, SigningBound C ∧ SteinitzBound C := sorry

/- AMBIGUITIES AND CHOICES
* Indexing: `v_1..v_N` is `Fin N → EuclideanSpace ℝ (Fin d)`; the prefix of length k is the sum over
  indices with `i.val < k`, k = 0..N (k=0 gives the empty sum 0). Permutation is `Equiv.Perm (Fin N)`.
* Signs as real numbers equal to 1 or -1 (avoids units coercions).
* "Absolute constant C": existential over ℝ outside the quantifiers over d, N, v. C is not required
  positive; it is forced to be ≥ 0 by k = 0 anyway (0 ≤ C√d).
* d, N ≥ 1 are hypotheses as in the source (d = 0 or N = 0 are excluded, no junk values used).
* ‖·‖₂ is the norm of EuclideanSpace. β and S₂(d) are not defined as sInf/sSup (would need
  conditionally-complete junk handling); the theorem is stated directly as existence of a permutation.
* "The constant in Thm 1.1 also suffices here" is read as: any C satisfying SigningBound also
  satisfies SteinitzBound. readingSameConstant states the weaker "one C works for both";
  readingConstantTransfers states the literal claim `∀ C', SigningBound C' → SteinitzBound C'`
  (together with existence of a Theorem 1.1 constant).
-/

/-- Literal form: whatever constant works for Theorem 1.1 works for Theorem 1.2. -/
theorem readingConstantTransfers : ∃ C : ℝ, SigningBound C ∧ ∀ C' : ℝ, SigningBound C' → SteinitzBound C' := sorry

end ReaderB
