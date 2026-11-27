import Mathlib

namespace ReaderB

open Classical

/-- `x^B`: flip exactly the coordinates in `B`. -/
def flipSet {n : ℕ} (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !x i else x i

/-- `s(f,x) = |{a | f(x^a) ≠ f(x)}|`. -/
noncomputable def sens {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun a : Fin n => f (flipSet x {a}) ≠ f x)).card

/-- `s(f) = max_x s(f,x)` (a `Finset.sup` over the nonempty finite cube; values are naturals so no junk). -/
noncomputable def s {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sens f)

/-- There are `m` pairwise disjoint nonempty blocks, each flipping the value of `f` at `x`. -/
def HasBlocks {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (m : ℕ) : Prop :=
  ∃ B : Fin m → Finset (Fin n), (∀ j, (B j).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ ∀ j, f (flipSet x (B j)) ≠ f x

/-- `bs(f,x)` = largest `m ≤ n` with `HasBlocks` (any valid `m` is `≤ n` since blocks are
disjoint and nonempty, so the bound `n` loses nothing; `m = 0` always works). -/
noncomputable def bsAt {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  Nat.findGreatest (HasBlocks f x) n

/-- `bs(f) = max_x bs(f,x)`. -/
noncomputable def bs {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.univ.sup (bsAt f)

/-- Theorem 1.1, first sentence. -/
theorem reading_thm_1_1_first :
    ∀ C : ℝ, 0 < C → ∃ n : ℕ, 0 < n ∧ ∃ f : (Fin n → Bool) → Bool,
      (∃ x y, f x ≠ f y) ∧ C * ((s f : ℝ) ^ 2) < (bs f : ℝ) := by
  sorry

/-- Theorem 1.1, "more precisely" sentence: for every `d ≥ 1` a nonconstant `f` with
`bs f / s f ^ 2 ≥ 2^d / (4 (d+2)^2)` (with `s f > 0` asserted so the quotient is not junk). -/
theorem reading_thm_1_1_precise :
    ∀ d : ℕ, 1 ≤ d → ∃ n : ℕ, 0 < n ∧ ∃ f : (Fin n → Bool) → Bool,
      (∃ x y, f x ≠ f y) ∧ 0 < s f ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤ (bs f : ℝ) / ((s f : ℝ) ^ 2) := by
  sorry

/-- Abstract's last sentence: a fixed `α > 2` and a family of nonconstant total Boolean functions
with unbounded block sensitivity and `bs f ≥ s f ^ α`. -/
theorem reading_abstract_alpha :
    ∃ α : ℝ, 2 < α ∧ ∃ (n : ℕ → ℕ) (f : ∀ k, (Fin (n k) → Bool) → Bool),
      (∀ k, ∃ x y, f k x ≠ f k y) ∧
      (∀ M : ℕ, ∃ k, M ≤ bs (f k)) ∧
      (∀ k, 0 < s (f k) ∧ (s (f k) : ℝ) ^ α ≤ (bs (f k) : ℝ)) := by
  sorry

/-
Ambiguities and choices.
* Boolean functions `(Fin n → Bool) → Bool`; `[n]` = `Fin n`. `x^B` = `flipSet`.
* s(f), bs(f): maxima as `Finset.sup` over all inputs (finite, nonempty cube, ℕ-valued, no junk).
  bs(f,x) via `Nat.findGreatest` bounded by `n`, harmless as argued in the docstring. Blocks are indexed
  by `Fin m` with pairwise-disjointness for distinct indices (so m blocks, not a set of blocks).
* ℕ-valued quantities are cast to ℝ before powers/products; no ℕ subtraction, no ⊤.
* "Nonconstant": `∃ x y, f x ≠ f y`. Positive `n` is required explicitly as in the text.
* The ratio in the "more precisely" part is stated with `0 < s f` added explicitly: the text divides by
  s(f)^2, which is positive for nonconstant f (a consequence), so this only rules out junk x/0.
* Third theorem: "our examples" read as an infinite sequence k ↦ f_k of nonconstant total Boolean functions
  (of varying arity n k) of the construction; "unbounded block sensitivity" read as: for every M some f_k has
  bs ≥ M (sup over the family is infinite); "bs(f) ≥ s(f)^α" for every member, with a single fixed real
  α > 2 chosen before the family (∃ α, ∃ family). `s (f k) > 0` included so the real power s^α is of a
  positive number (not 0^α junk). Note this reading is a strong one: alpha is uniform over the family.
-/

end ReaderB
