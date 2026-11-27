import Mathlib

namespace ReaderC

/-- `x^B`: flip exactly the coordinates in `B`. Inputs are `Fin n → Bool` (the cube `{0,1}^n`,
with `Bool` for `{0,1}`). -/
def flipSet {n : ℕ} (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !x i else x i

/-- Sensitivity at `x`: `#{a : f(x^a) ≠ f(x)}`. Natural-number valued, no junk. -/
def sens {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun a : Fin n => f (flipSet x {a}) ≠ f x).card

/-- Sensitivity `s(f) = max_x s(f, x)`. -/
def sensFn {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sens f)

/-- Block sensitivity at `x`: the largest `m` such that there are `m` pairwise disjoint nonempty
sets `B_1, …, B_m ⊆ [n]` with `f(x^{B_j}) ≠ f(x)`. Taken as `sSup` of the set of such `m`;
that set contains `0` and is bounded by `n`, so the `sSup` is the maximum. -/
noncomputable def bsAt {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  sSup {m : ℕ | ∃ B : Fin m → Finset (Fin n),
    (∀ j, (B j).Nonempty) ∧ (∀ j k, j ≠ k → Disjoint (B j) (B k)) ∧
      ∀ j, f (flipSet x (B j)) ≠ f x}

/-- Block sensitivity `bs(f) = max_x bs(f, x)`. -/
noncomputable def bsFn {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.univ.sup (bsAt f)

/-- Nonconstant. -/
def Nonconst {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

/-- First sentence of Theorem 1.1: for every real `C > 0` there are a positive integer `n` and
a nonconstant total Boolean function with `bs(f) > C s(f)^2`. -/
theorem reading_theorem_1_1_first :
    ∀ C : ℝ, 0 < C → ∃ n : ℕ, 0 < n ∧ ∃ f : (Fin n → Bool) → Bool,
      Nonconst f ∧ (bsFn f : ℝ) > C * ((sensFn f : ℝ)) ^ 2 := sorry

/-- The "More precisely" sentence: for every integer `d ≥ 1` the construction gives a nonconstant
total Boolean function `f` with `bs(f)/s(f)^2 ≥ 2^d / (4 (d+2)^2)`. The condition
`0 < s(f)` is stated explicitly, so the quotient never divides by `0`. -/
theorem reading_theorem_1_1_more_precisely :
    ∀ d : ℕ, 1 ≤ d → ∃ n : ℕ, 0 < n ∧ ∃ f : (Fin n → Bool) → Bool,
      Nonconst f ∧ 0 < sensFn f ∧
      (bsFn f : ℝ) / ((sensFn f : ℝ)) ^ 2
        ≥ (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) := sorry

/-- The abstract's last sentence: for some fixed `α > 2`, the examples have unbounded block
sensitivity and satisfy `bs(f) ≥ s(f)^α`. Reading: there is one family of nonconstant total
Boolean functions `F k` (on `Fin (N k)`) which is unbounded in `bs` and satisfies the
inequality for every member. -/
theorem reading_abstract_alpha :
    ∃ α : ℝ, 2 < α ∧
      ∃ (N : ℕ → ℕ) (F : ∀ k, (Fin (N k) → Bool) → Bool),
        (∀ k, Nonconst (F k)) ∧
        (∀ M : ℕ, ∃ k, M ≤ bsFn (F k)) ∧
        ∀ k, (bsFn (F k) : ℝ) ≥ ((sensFn (F k) : ℝ)) ^ α := sorry

/-!
## Ambiguities and choices

1. Domain and range: `{0,1}^n` is `Fin n → Bool`, and `{0,1}` is `Bool`. Totality means `f` is
   defined on all of `Fin n → Bool`.
2. Sensitivity: `s(f,x) = #{a : f(x^a) ≠ f(x)}` is a `Finset.card`, natural-valued, with no
   junk. `s(f) = max_x s(f,x)` is `Finset.univ.sup`, the maximum over the finite cube.
3. Block sensitivity: `bs(f,x)` is the `sSup` of the set of `m` for which there exist `m`
   pairwise disjoint nonempty blocks, each flipped to a different value. The set is nonempty
   (it contains `0`, via the empty family) and bounded by `n` (disjoint nonempty subsets of
   `Fin n`), so `sSup` is the maximum and no `sSup ∅` or unbounded junk arises.
   Disjointness is `Disjoint` on `Finset`s for `j ≠ k`.
4. `x^B` (`flipSet`) flips the coordinates of `B` and keeps the others. `x^a` is `x^{{a}}`.
5. Theorem 1.1, first sentence: "for every real `C > 0` there are a positive integer `n` and a
   nonconstant total Boolean `f` with `bs(f) > C s(f)^2`". I quantify `n` over `ℕ` with
   `0 < n`, and `C` over `ℝ` with `0 < C`. The `s(f)^2` is real, cast from `ℕ`, and
   `bs(f) > C s(f)^2` is real comparison.
6. Theorem 1.1, "More precisely": "for every integer `d ≥ 1` the construction below gives a
   nonconstant total Boolean `f` with `bs(f)/s(f)^2 ≥ 2^d/(4(d+2)^2)`". The text refers to
   "the construction below", which is not in the excerpt I read. So I read it as: for each
   `d ≥ 1`, there exist `n` and a nonconstant total `f` with that inequality. The quotient is
   written with the explicit clause `0 < s(f)`, so no `x/0 = 0` value can satisfy it. For
   nonconstant `f`, `s(f) ≥ 1` anyway (a nonconstant function on the cube has a flipped edge),
   so the clause is not a restriction.
   The bound `2^d/(4(d+2)^2)` is computed in `ℝ`: `(2:ℝ)^d` and `((d:ℝ)+2)^2`, with `d`
   cast from `ℕ`. The power `^ d` in `(2:ℝ)^d` is a natural-number power, not a real power.
7. Third theorem (the abstract's last sentence): "for some fixed `α > 2`, our examples have
   unbounded block sensitivity and satisfy `bs(f) ≥ s(f)^α`". "Our examples" does not
   name a set in the excerpt I read. I take it as one indexed family `F k` (on `Fin (N k)`) of
   nonconstant total functions. "Unbounded block sensitivity" is `∀ M, ∃ k, M ≤ bs(F k)`.
   The inequality is required for every member of the family. This is the weakest reading
   consistent with the wording: the construction in the text may give a different family, and
   the family-existence form here quantifies over all families with these properties.
   `α` is a real exponent, `2 < α`. `s(F k) ≥ 1` for nonconstant functions, so the real
   power `(s : ℝ) ^ α` has a positive base and no real-power junk occurs (`0 ^ α` for
   `α > 0` would be `0`, which is never reached here).
8. Natural subtraction and division: none occurs. The only division is the explicit ratio in
   the "More precisely" theorem, guarded by `0 < s(f)`.
9. `sSup`, `sup` on `ℕ`: used only for block sensitivity (bounded, nonempty, see item 3) and
   the maximum over `Fin n → Bool` (finite, nonempty for `n ≥ 0`).
-/

end ReaderC
