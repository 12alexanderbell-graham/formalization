import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

open Filter Asymptotics

namespace ReaderB

abbrev P : Type := EuclideanSpace ℝ (Fin 2)

/-- u(X): number of unordered pairs {x,y} ⊆ X with ‖x-y‖₂ = 1 (as a set of `Sym2` elements). -/
noncomputable def u (X : Finset P) : ℕ :=
  {z : Sym2 P | ∃ x ∈ X, ∃ y ∈ X, z = s(x, y) ∧ dist x y = 1}.ncard

/-- u(n) = max over n-point subsets of ℝ². -/
noncomputable def un (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ X : Finset P, X.card = n ∧ u X = k}

theorem reading_thm_1_1 :
    ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < 4 / 3 ∧ ∀ n : ℕ, (un n : ℝ) ≤ C * (n : ℝ) ^ β := sorry

theorem reading_equiv :
    ∃ δ : ℝ, 0 < δ ∧ (fun n : ℕ => (un n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (4 / 3 - δ)) :=
  sorry

end ReaderB

/-
Ambiguities / choices
- ℝ² is `EuclideanSpace ℝ (Fin 2)`, whose `dist` is the Euclidean (ℓ²) distance.
- Finite sets as `Finset`; |X| = n is `X.card = n`. Unordered pairs as `Sym2`; s(x,y) with dist = 1 forces x ≠ y,
  so endpoints are distinct automatically and each pair is counted once.
- u(n) is a max; defined as `sSup` in ℕ of the set of values. Junk risk: sSup on ℕ gives 0 if unbounded,
  but the set is bounded (≤ n², and nonempty since ℝ² has n-point sets), so it is the true max. Not proved.
- n ranges over all naturals including 0 (0^β = 0 for β ≥ 1, and u(0)=0, consistent with the source).
- "Absolute constants" = existential over reals C, β with 0<C, 1≤β<4/3, not depending on n.
- Equivalent form: ∃ δ>0 with u(n)=O(n^{4/3-δ}) as n→∞ (atTop on ℕ), real rpow. I state it as a separate
  existence statement; the equivalence of the two is not formalised as an iff.
-/

-- ===== reader C =====

/-!
Reading of O18 (unitdist), from `00-introduction.tex` lines 1-20 only.
-/

open Finset Filter Asymptotics

namespace ReaderC

namespace UnitDist

/-- The Euclidean plane `ℝ²` with its Euclidean distance `‖x - y‖₂`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The unordered pairs `{x, y} ⊂ X` of distinct points at distance 1, as 2-element subsets. -/
noncomputable def unitPairs (X : Finset Plane) : Finset (Finset Plane) :=
  (X.powersetCard 2).filter (fun s => ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ dist x y = 1)

/-- `u(X)`: the number of unordered pairs of distinct points of `X` at distance 1. -/
noncomputable def u (X : Finset Plane) : ℕ :=
  (unitPairs X).card

/-- `u(n) = max { u(X) : X ⊂ ℝ², |X| = n }`. The set of values is a subset of `{0, …, C(n,2)}`,
so it is finite and `sSup` is its maximum. -/
noncomputable def uMax (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ u X = m}

/-- Theorem 1.1 (reading), main bound: there are absolute constants `0 < C < ∞` and
`1 ≤ β < 4/3` with `u(n) ≤ C n^β` for every nonnegative integer `n`. -/
theorem reading_unitdist_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ β : ℝ, 1 ≤ β ∧ β < 4 / 3 ∧
      ∀ n : ℕ, (uMax n : ℝ) ≤ C * (n : ℝ) ^ β := by
  sorry

/-- Theorem 1.1 (reading), the "equivalently" form: `u(n) = O(n^{4/3 - δ})` for an absolute
`δ > 0`. Stated as Landau big-O along `n → ∞`. -/
theorem reading_unitdist_bigO :
    ∃ δ : ℝ, 0 < δ ∧
      (fun n : ℕ => (uMax n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (4 / 3 - δ)) := by
  sorry

end UnitDist

end ReaderC

/-!
Ambiguities and choices (O18, unitdist):

1. Plane. `ℝ²` is `EuclideanSpace ℝ (Fin 2)`, so `dist` is the Euclidean norm `‖x-y‖₂`
   as the source writes. `ℝ × ℝ` would have the sup metric, which is wrong here.
2. Pairs. `u(X)` counts 2-element subsets `{x, y} ⊂ X` with `dist x y = 1`. The
   `∃ x ∈ s, ∃ y ∈ s, x ≠ y` clause encodes "endpoints are distinct" and unordered pairs.
   On a 2-element set this is exactly `dist` of the two points being 1.
3. `u(n)` is `sSup` over the values `u X` for `X` with `X.card = n`. For each `n` the set of
   values is bounded by `C(n,2)`, and nonempty since `n`-point sets exist. So `sSup` is the
   maximum, not a junk value. For `n = 0` and `n = 1` the value is `0`, as expected.
4. Theorem 1.1 says "absolute constants `0 < C < ∞`", so `C : ℝ` with `0 < C` is the formal
   version of finiteness. `β` is real with `1 ≤ β < 4/3`. `(n:ℝ)^β` is real `rpow`. At
   `n = 0` it is `0`, which is harmless since `uMax 0 = 0`.
5. "Equivalently" is stated as a separate theorem, `reading_unitdist_bigO`, with `IsBigO`
   along `atTop`. I read the source's "for an absolute δ > 0" as `∃ δ > 0`. The source's
   "equivalently" is taken as an assertion to formalise, not something I proved. The
   `O(·)` form is asserted as a separate reading theorem, not derived from the bound.
6. I did not add a restriction on `n` beyond "every nonnegative integer", as the source says.
-/
