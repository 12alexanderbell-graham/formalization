import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

open scoped BigOperators

/-- `ℝ^d` with the Euclidean norm `‖·‖₂`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The `k`-th prefix sum `∑_{i=1}^k w_i` of a sequence `w_1, …, w_N`, indexed here by `Fin N`
(so source index `i` is `Fin` index `i - 1`). For `k = 0` it is the empty sum `0`. -/
noncomputable def prefixSum {d N : ℕ} (w : Fin N → Euc d) (k : ℕ) : Euc d :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), w i

/-- The statement of Theorem 1.1 for a given constant `C`: for all `d, N ≥ 1` and every
`v_1, …, v_N ∈ ℝ^d` in the unit ball there are signs `ε_i ∈ {-1, 1}` with
`max_{0 ≤ k ≤ N} ‖∑_{i ≤ k} ε_i v_i‖₂ ≤ C √d`. -/
def SigningBound (C : ℝ) : Prop :=
  ∀ d N : ℕ, 1 ≤ d → 1 ≤ N →
    ∀ v : Fin N → Euc d, (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin N → ℝ, (∀ i, ε i = -1 ∨ ε i = 1) ∧
        ∀ k : ℕ, k ≤ N → ‖prefixSum (fun i => ε i • v i) k‖ ≤ C * Real.sqrt d

/-- The statement of Theorem 1.2 for a given constant `C`: for all `d, N ≥ 1` and every
zero-sum family `v_1, …, v_N ∈ ℝ^d` in the unit ball some permutation `π ∈ 𝔖_N` has
`max_{0 ≤ k ≤ N} ‖∑_{i ≤ k} v_{π(i)}‖₂ ≤ C √d`. -/
def SteinitzBound (C : ℝ) : Prop :=
  ∀ d N : ℕ, 1 ≤ d → 1 ≤ N →
    ∀ v : Fin N → Euc d, (∀ i, ‖v i‖ ≤ 1) → ∑ i, v i = 0 →
      ∃ π : Equiv.Perm (Fin N),
        ∀ k : ℕ, k ≤ N → ‖prefixSum (fun i => v (π i)) k‖ ≤ C * Real.sqrt d

/-- Theorem 1.1 (Prescribed-order signed prefixes). -/
theorem reading_thm_1_1_signing : ∃ C : ℝ, SigningBound C := sorry

/-- Theorem 1.2 (Euclidean Steinitz–Bergström bound). -/
theorem reading_thm_1_2_steinitz : ∃ C : ℝ, SteinitzBound C := sorry

/-- Theorem 1.2, last sentence: "The constant in Theorem 1.1 also suffices here" — one `C`
works for both theorems. Read as: every constant valid for Theorem 1.1 is valid for 1.2. -/
theorem reading_thm_1_2_same_constant : ∀ C : ℝ, SigningBound C → SteinitzBound C := sorry

/-- Weaker reading of the same sentence: a single `C` for both. -/
theorem reading_thm_1_1_and_1_2_one_constant : ∃ C : ℝ, SigningBound C ∧ SteinitzBound C := sorry

end ReaderA

/-
Ambiguities and choices (reader A).

1. Ambient space. `ℝ^d` with `‖·‖₂` is `EuclideanSpace ℝ (Fin d)`, whose norm is the Euclidean
   (L²) norm. Not `Fin d → ℝ`, which carries the sup norm in Mathlib (that would be a junk reading).

2. Indexing. The source's `v_1, …, v_N` become `v : Fin N → Euc d` (0-based). The prefix
   `∑_{i=1}^k` is the sum over `Fin` indices `i` with `i.val < k`; `k = 0` gives the empty sum `0`,
   matching "an empty sum is zero". `max_{0 ≤ k ≤ N} … ≤ C√d` is rendered as
   `∀ k ≤ N, … ≤ C√d` (equivalent, since the max over a finite nonempty range is ≤ a bound iff
   every term is).

3. Signs. `ε_i ∈ {-1, 1}` is a real-valued `ε : Fin N → ℝ` with `ε i = -1 ∨ ε i = 1` and the
   signed vector is `ε i • v i`. (Using `ℤˣ` would be equivalent.)

4. Permutations. `𝔖_N` is `Equiv.Perm (Fin N)`; `v_{π(i)}` is `v (π i)`, and the `k`-th prefix
   sums the first `k` positions of the reordered family.

5. Constant. "There is an absolute constant C" is `∃ C : ℝ` quantified before `d, N, v`, so `C`
   is independent of `d`, `N` and the sequence. I do not require `C > 0`: the source does not
   say so, the claims force `C ≥ 0` anyway (e.g. `d = N = 1`, `v = 0`, `k = 0`), and any valid
   `C` can be enlarged. `d, N ≥ 1` are kept as explicit hypotheses as in the source.

6. "The constant in Theorem 1.1 also suffices here." Two readings, both stated:
   (a) `reading_thm_1_2_same_constant`: any `C` that works for Theorem 1.1 works for 1.2
       (the strong, literal reading: "the constant" = whatever constant 1.1 provides);
   (b) `reading_thm_1_1_and_1_2_one_constant`: there is one `C` valid for both.
   (a) together with `reading_thm_1_1_signing` implies (b). The intended proof (signing ⇒
   Steinitz via a standard reduction) may lose a factor depending on the exact reduction; if the
   authors only meant (b) then (a) is a strengthening. I regard (b) as the safe reading and (a)
   as the most literal one.

7. `β` and `S_2(d)` are defined in the source only as motivation; they are not needed for the
   two theorems, so I did not formalize them. (`S_2(d) = O(√d)` is equivalent to
   `reading_thm_1_2_steinitz` modulo the case `N = 0`, where the family is empty and β = 0.)

No junk values: no division, no `sInf/sSup`, no truncated subtraction appear; `Real.sqrt d` is
applied to `d ≥ 1`.
-/

-- ===== reader B =====

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

-- ===== reader C =====

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
