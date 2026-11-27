import Mathlib

namespace ReaderC

/-- Prefix sum of the first `k` terms `w 0, …, w (k-1)` of a family indexed by `Fin N`.
Written as the sum over the indices `i` with `i < k`; for `k ≤ N` this is the `k`-th partial sum. -/
def prefixSum {N : ℕ} {E : Type} [AddCommGroup E] (w : Fin N → E) (k : ℕ) : E :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), w i

/-- Theorem 1.1 (Prescribed-order signed prefixes). -/
theorem reading_thm_1_1_signing :
    ∃ C : ℝ, ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
      ∀ v : Fin N → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ ≤ 1) →
        ∃ ε : Fin N → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ k : ℕ, k ≤ N →
            ‖prefixSum (fun i => ε i • v i) k‖ ≤ C * Real.sqrt d := by
  sorry

/-- Theorem 1.2 (Euclidean Steinitz–Bergström bound). -/
theorem reading_thm_1_2_steinitz :
    ∃ C : ℝ, ∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
      ∀ v : Fin N → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ ≤ 1) → ∑ i, v i = 0 →
        ∃ π : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
          ‖prefixSum (fun i => v (π i)) k‖ ≤ C * Real.sqrt d := by
  sorry

/-- "The constant in Theorem 1.1 also suffices here": the same real `C` that works for the
signing statement also works for the Steinitz statement. -/
theorem reading_same_constant_steinitz :
    ∀ C : ℝ,
      (∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
        ∀ v : Fin N → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ ≤ 1) →
          ∃ ε : Fin N → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
            ∀ k : ℕ, k ≤ N →
              ‖prefixSum (fun i => ε i • v i) k‖ ≤ C * Real.sqrt d) →
      (∀ (d N : ℕ), 1 ≤ d → 1 ≤ N →
        ∀ v : Fin N → EuclideanSpace ℝ (Fin d), (∀ i, ‖v i‖ ≤ 1) → ∑ i, v i = 0 →
          ∃ π : Equiv.Perm (Fin N), ∀ k : ℕ, k ≤ N →
            ‖prefixSum (fun i => v (π i)) k‖ ≤ C * Real.sqrt d) := by
  sorry

/-
Ambiguities and choices (Steinitz family, source lines 1-45 of introduction.tex):

* "Euclidean unit ball of R^d" is read as `‖v i‖ ≤ 1` in `EuclideanSpace ℝ (Fin d)`
  (Euclidean norm); the ball is closed, as in the source's `\le 1`.
* "Integers d, N ≥ 1" is read as `1 ≤ d`, `1 ≤ N` in `ℕ`; the family is `v : Fin N → ℝ^d`
  (an indexed family, repetitions allowed).
* Signs `ε_i ∈ {-1, 1}` are real numbers `ε i : ℝ` with `ε i = 1 ∨ ε i = -1`, acting by scalar
  multiplication on the vectors. (Alternative `ℤ`-valued signs would give the same statement.)
* "max over 0 ≤ k ≤ N" is read as `∀ k : ℕ, k ≤ N → ...`, using the prefix sum `prefixSum`
  (sum over indices `i < k`, so the empty prefix is zero).
* Theorem 1.1 says "there is an absolute constant C such that for all d, N, v ..., there are
  signs ...": this is `∃ C : ℝ, ∀ d N v, ... ∃ ε, ...`. The constant is an arbitrary real `C`,
  not required to be positive; a non-positive C would make the conclusion false, so this is
  harmless. The bound is `C * Real.sqrt d` (the source's `C\sqrt d`).
* Theorem 1.2: "some permutation π ∈ S_N" is `Equiv.Perm (Fin N)`. The zero-sum hypothesis is
  `∑ i, v i = 0`. The permuted family is `fun i => v (π i)`.
* The Steinitz constant β, S_2(d) and the conjecture are definitions/remarks in the source, not
  claims of the two theorems; I did not formalize them (the brief asks only for Thm 1.1, Thm 1.2
  and the shared-constant remark).
* "The constant in Theorem 1.1 also suffices here" is read as: for every real `C`, if the
  signing statement of Theorem 1.1 holds with `C`, then the Steinitz statement of Theorem 1.2
  holds with the same `C`. Stated as `∀ C, (signing with C) → (Steinitz with C)`.
  This is the reading of "one C for both".
-/

end ReaderC
