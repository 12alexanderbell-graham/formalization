import Mathlib

namespace ReaderA

open Filter Asymptotics

noncomputable section

/-- The Euclidean plane `ℝ²` with the Euclidean norm `‖·‖₂`. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- `u(X) = #{ {x,y} ⊆ X : ‖x - y‖₂ = 1 }` for a finite `X ⊆ ℝ²`: the number of unordered
pairs (2-element subsets) `{x, y}` of `X` whose two points are at Euclidean distance `1`.
A 2-element subset has distinct endpoints; for such a subset `s = {a, b}` the condition
"some `x, y ∈ s` have `‖x - y‖ = 1`" is equivalent to `‖a - b‖ = 1`, because `x = y` gives
norm `0 ≠ 1`. -/
def u (X : Finset Plane) : ℕ :=
  ((X.powersetCard 2).filter (fun s => ∃ x ∈ s, ∃ y ∈ s, ‖x - y‖ = 1)).card

/-- The set of values `u(X)` over `n`-point sets `X ⊆ ℝ²`. -/
def uValues (n : ℕ) : Set ℕ := {m | ∃ X : Finset Plane, X.card = n ∧ u X = m}

/-- `u(n) = max_{X ⊆ ℝ², |X| = n} u(X)`, written as a supremum in `ℕ`. -/
def uMax (n : ℕ) : ℕ := sSup (uValues n)

/-- No junk: `u(X) ≤ (|X| choose 2)`. -/
theorem u_le_choose (X : Finset Plane) : u X ≤ X.card.choose 2 := by
  unfold u
  calc _ ≤ (X.powersetCard 2).card := Finset.card_filter_le _ _
    _ = X.card.choose 2 := Finset.card_powersetCard _ _

/-- No junk: the set of values is bounded above (by `n choose 2`), so the `sSup` is a genuine
maximum whenever the set is nonempty (and it is nonempty since `ℝ²` is infinite). -/
theorem bddAbove_uValues (n : ℕ) : BddAbove (uValues n) := by
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨X, hX, rfl⟩
  simpa [hX] using u_le_choose X

/-- Theorem 1.1: there are absolute constants `0 < C < ∞` and `1 ≤ β < 4/3` such that
`u(n) ≤ C n^β` for every nonnegative integer `n`. -/
theorem reading_thm_1_1 :
    ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < 4 / 3 ∧
      ∀ n : ℕ, (uMax n : ℝ) ≤ C * (n : ℝ) ^ β := sorry

/-- The "equivalently" form: `u(n) = O(n^{4/3 - δ})` for an absolute `δ > 0`. -/
theorem reading_thm_1_1_bigO :
    ∃ δ : ℝ, 0 < δ ∧
      (fun n : ℕ => (uMax n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3 - δ)) := sorry

end

end ReaderA

/-
Ambiguities and choices (Reader A, O18 unitdist):

1. ℝ² and ‖·‖₂: `EuclideanSpace ℝ (Fin 2)`, whose norm is the Euclidean (L²) norm. (Not
   `ℝ × ℝ`, whose Mathlib norm is the sup norm.)

2. u(X): "#{{x,y} ⊂ X : ‖x−y‖₂ = 1}", "pairs are unordered and their endpoints are distinct".
   I count 2-element subsets s of X (`X.powersetCard 2`) for which some x, y ∈ s satisfy
   ‖x − y‖ = 1; for s = {a, b} with a ≠ b this is exactly ‖a − b‖ = 1. The "⊂" in the source
   is read as "⊆" (a subset of X), as is standard. X is a `Finset`, matching "finite set".

3. u(n) = max over |X| = n: written `sSup` in ℕ of {u(X) : |X| = n}. Junk avoidance: in ℕ,
   `sSup` of an unbounded set or of ∅ is 0; I prove `bddAbove_uValues` (bound n choose 2), and
   the set is nonempty because ℝ² has n-point subsets for every n (not proved in the file, but
   true), so `uMax n` is the genuine maximum. An equivalent max-free reading would be
   "∀ X, |X| = n → u(X) ≤ C n^β".

4. "absolute constants 0 < C < ∞ and 1 ≤ β < 4/3": ∃ C β : ℝ before ∀ n (so independent of n
   and of the configuration). C < ∞ is automatic for a real C.

5. n^β: real power `(n : ℝ) ^ β` (`Real.rpow`). For n = 0 this is 0 (β ≥ 1 > 0) and u(0) = 0,
   so "every nonnegative integer n" including n = 0 is fine.

6. The "equivalently" form: u(n) = O(n^{4/3−δ}) read as Landau big-O as n → ∞ along ℕ
   (`Asymptotics.IsBigO atTop`), with ∃ δ > 0 absolute (quantified first). No upper bound on
   δ is imposed. It is stated as a second, separate reading theorem; its equivalence with the
   first form (take δ = 4/3 − β; conversely β = max(1, 4/3 − δ') with small n absorbed into C)
   is not proved here.
-/
