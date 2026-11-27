import Mathlib

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
