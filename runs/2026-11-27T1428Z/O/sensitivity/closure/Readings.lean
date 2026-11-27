import Mathlib

/-! # Target O, family sensitivity: the three blind readings of run 2026-11-27T1428Z (brief 7bfe069), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Blind reading (reader A) of the abstract and introduction of
"A superquadratic separation of sensitivity and block sensitivity":
Theorem 1.1 (two sentences) and the abstract's last sentence.
-/

namespace ReaderA

open Classical in
/-- `x^B`: flip precisely the coordinates in `B`.  Coordinates are indexed by `Fin n`
(standing for `[n] = {1, …, n}`). -/
def flipSet {n : ℕ} (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !x i else x i

/-- `s(f, x) = |{a ∈ [n] : f(x^a) ≠ f(x)}|`. -/
def sensAt {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun a : Fin n => f (flipSet x {a}) ≠ f x).card

/-- `s(f) = max_x s(f, x)` (a finite max; `Finset.sup` over all inputs). -/
def sens {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensAt f)

/-- A family of pairwise disjoint nonempty blocks `B_j ⊆ [n]`, each with `f(x^{B_j}) ≠ f(x)`. -/
def IsSensitiveBlockFamily {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (P : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ P, B.Nonempty ∧ f (flipSet x B) ≠ f x) ∧ (P : Set (Finset (Fin n))).PairwiseDisjoint id

open Classical in
/-- `bs(f, x)`: the largest `m` such that there are pairwise disjoint nonempty
`B_1, …, B_m ⊆ [n]` with `f(x^{B_j}) ≠ f(x)` for all `j`.  A finite max over all such families
(the empty family is always admissible, so the max is over a nonempty finite set). -/
noncomputable def bsAt {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (IsSensitiveBlockFamily f x)).sup Finset.card

/-- `bs(f) = max_x bs(f, x)`. -/
noncomputable def bs {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  Finset.univ.sup (bsAt f)

/-- `f` is nonconstant. -/
def Nonconstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

/-- Theorem 1.1, first sentence: for every real `C > 0` there are a positive integer `n` and a
nonconstant total Boolean function `f : {0,1}^n → {0,1}` with `bs(f) > C s(f)^2`. -/
theorem reading_thm_1_1 (C : ℝ) (hC : 0 < C) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : (Fin n → Bool) → Bool,
      Nonconstant f ∧ (bs f : ℝ) > C * (sens f : ℝ) ^ 2 := by
  sorry

/-- Theorem 1.1, "More precisely": for every integer `d ≥ 1` there is a nonconstant total Boolean
function `f` (on some positive number `n` of inputs) with `bs(f)/s(f)^2 ≥ 2^d / (4(d+2)^2)`.
The conjunct `0 < s(f)` (a consequence of nonconstancy) makes explicit that the division is not
by zero. -/
theorem reading_thm_1_1_precise (d : ℕ) (hd : 1 ≤ d) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : (Fin n → Bool) → Bool,
      Nonconstant f ∧ 0 < sens f ∧
        (bs f : ℝ) / (sens f : ℝ) ^ 2 ≥ (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) := by
  sorry

/-- Abstract, last sentence: for some fixed `α > 2`, the examples (nonconstant total Boolean
functions) have unbounded block sensitivity and satisfy `bs(f) ≥ s(f)^α`.  Read as: there is a
real `α > 2` such that the class of nonconstant total Boolean functions `f` with
`bs(f) ≥ s(f)^α` has unbounded block sensitivity, i.e. for every bound `M` some such `f` has
`bs(f) > M`.  `0 < s(f)` is made explicit so the real power has a positive base. -/
theorem reading_abstract :
    ∃ α : ℝ, 2 < α ∧ ∀ M : ℕ, ∃ n : ℕ, 0 < n ∧ ∃ f : (Fin n → Bool) → Bool,
      Nonconstant f ∧ 0 < sens f ∧ M < bs f ∧ (sens f : ℝ) ^ α ≤ (bs f : ℝ) := by
  sorry

end ReaderA

/-!
## Ambiguities and choices (reader A)

* `{0,1}` is `Bool`; `[n] = {1,…,n}` is modelled by `Fin n = {0,…,n-1}` (a relabelling).
  Total Boolean function = an arbitrary function `(Fin n → Bool) → Bool`.
* `x^B` flips exactly the coordinates in `B`; `x^a = x^{{a}}`.
* `s(f) = max_x s(f,x)` and `bs(f) = max_x bs(f,x)` are `Finset.sup` over the finite set of
  inputs (ℕ-valued, `⊥ = 0`, never reached as junk since the input set is nonempty for every
  `n`, including `n = 0`).  `bs(f,x)` is a `Finset.sup` of cardinalities over all admissible
  families; the family `B_1,…,B_m` is represented as a `Finset` of blocks: since the blocks are
  pairwise disjoint and nonempty they are automatically distinct, so a list of `m` blocks and
  a set of `m` blocks carry the same information.  The empty family (`m = 0`) is admissible,
  so the max is over a nonempty finite set; no `sSup` is used anywhere.  Mathlib has no
  sensitivity/block-sensitivity notions, so these are defined here.
* "nonconstant": `∃ x y, f x ≠ f y`.
* First sentence of Theorem 1.1: `n` positive integer is `0 < n`; `C` real, `C > 0`; the
  inequality is in `ℝ` with `s(f)^2` a natural power.
* "More precisely … the construction below gives a nonconstant total Boolean function `f`":
  the construction is not in the excerpt, so this is read existentially (some `n > 0` and some
  nonconstant `f`) for each integer `d ≥ 1`.  The ratio is real division.  Junk avoidance
  (`x/0 = 0`): a nonconstant `f` has `s(f) ≥ 1` (walk from `x` to `y` one bit at a time; some
  step changes the value), so I add the conjunct `0 < s(f)`, which is implied by
  `Nonconstant f` and therefore does not change the statement's strength; it only makes the
  denominator's positivity visible.  `2^d` is a natural power in `ℝ`; `4(d+2)^2` is computed in
  `ℝ` (no ℕ subtraction anywhere).
* Abstract's last sentence: "our examples" is read as "some class of nonconstant total Boolean
  functions (on arbitrary numbers of inputs)"; "for some fixed α > 2" is one real `α` chosen
  before the examples; "unbounded block sensitivity" is quantified as: for every natural bound
  `M` there is an example with `bs(f) > M`; "satisfy bs(f) ≥ s(f)^α" holds for each of those
  examples.  Equivalently: there is a sequence of nonconstant functions with `bs → ∞` along a
  subsequence and `bs ≥ s^α` throughout.  `s(f)^α` is `Real.rpow`; junk avoidance: the base is
  `s(f) ≥ 1 > 0` (made explicit by the conjunct `0 < s(f)`, implied by nonconstancy), so no
  real power of a nonpositive number is taken.  Without that conjunct the reading would be the
  same, since nonconstant implies `s(f) ≥ 1`.
-/


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
