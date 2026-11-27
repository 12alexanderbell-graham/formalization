import Mathlib

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
