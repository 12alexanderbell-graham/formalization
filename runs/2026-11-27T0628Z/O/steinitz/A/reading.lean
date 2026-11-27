import Mathlib

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
