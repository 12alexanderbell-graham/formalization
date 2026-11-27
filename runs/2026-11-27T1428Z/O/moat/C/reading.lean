import Mathlib

namespace ReaderC

/-- A Gaussian prime: an irreducible element of `ℤ[i] = GaussianInt`. -/
def IsGaussianPrime (z : GaussianInt) : Prop := Irreducible z

/-- Euclidean distance `|z - w| = √(N(z - w))` on `ℤ[i] ≅ ℤ²`, with `a + bi ↦ (a, b)`. -/
noncomputable def gdist (z w : GaussianInt) : ℝ :=
  Real.sqrt ((((z.re - w.re : ℤ) : ℝ)) ^ 2 + (((z.im - w.im : ℤ) : ℝ)) ^ 2)

/-- Edge of `G_D` between distinct `z, w` with `|z - w| ≤ D`. -/
def adjD (D : ℝ) (z w : GaussianInt) : Prop := z ≠ w ∧ gdist z w ≤ D

/-- `G_D`: vertices are the Gaussian primes, edges as in `adjD` between Gaussian primes. -/
def GD (D : ℝ) (z w : GaussianInt) : Prop :=
  IsGaussianPrime z ∧ IsGaussianPrime w ∧ adjD D z w

/-- The connected component of `z` in `G_D`, as a set of vertices. -/
def componentOf (D : ℝ) (z : GaussianInt) : Set GaussianInt :=
  {w | IsGaussianPrime w ∧ Relation.ReflTransGen (GD D) z w}

/-- Theorem 1.1: for every real `D` there is a natural `B` bounding the number of vertices of
every connected component of `G_D`. `encard` is used, so an infinite component would
give `⊤` and not a fake small number. -/
theorem reading_moat_thm1_1 :
    ∀ D : ℝ, ∃ B : ℕ, ∀ z : GaussianInt, IsGaussianPrime z →
      (componentOf D z).encard ≤ (B : ℕ∞) := by
  sorry

/-- "Consequently": every sequence of distinct Gaussian primes with successive distances at
most `D` has at most `B` terms (the same `B` as the theorem, depending on `D`). -/
theorem reading_moat_consequently :
    ∀ D : ℝ, ∃ B : ℕ, ∀ (n : ℕ) (p : Fin n → GaussianInt),
      Function.Injective p → (∀ i, IsGaussianPrime (p i)) →
      (∀ i j : Fin n, j.val = i.val + 1 → gdist (p i) (p j) ≤ D) →
      n ≤ B := by
  sorry

/-- Answer to the infinite-walk question: for no real `D` does `G_D` contain an infinite path
with no repeated vertex (an injective sequence of Gaussian primes with consecutive vertices
adjacent in `G_D`). -/
theorem reading_moat_no_infinite_path :
    ∀ D : ℝ, ¬ ∃ p : ℕ → GaussianInt, Function.Injective p ∧
      (∀ n, IsGaussianPrime (p n)) ∧ ∀ n, GD D (p n) (p (n + 1)) := by
  sorry

/-!
## Ambiguities and choices (reader C, O46)

1. Gaussian primes: "irreducible element of `ℤ[i]`", read literally as `Irreducible z` in
   Mathlib's `GaussianInt` (`Zsqrtd (-1)`). In a UFD this is the same as prime, but I kept the
   source's word.

2. Coordinates: `a + bi ↦ (a, b)` via `z.re`, `z.im`. The distance is the Euclidean one,
   `gdist z w = √((Δa)² + (Δb)²)`, computed in `ℝ` (the integer differences are cast to
   `ℝ` before squaring, so no `ℤ`-subtraction junk). `gdist` is `Real.sqrt`, so a negative
   `D` gives no edges; this matches "`|z - w| ≤ D`" for every real `D`.

3. "Finite real D": I quantified over all reals `D` (every real is finite in this sense).
   For `D < 0`, the edge relation is empty and the statements remain true.

4. Edges: `G_D` has the Gaussian primes as vertices, and an edge between DISTINCT `z, w` with
   `|z - w| ≤ D`. `adjD` requires `z ≠ w`. The graph `G_D` is `GD`, which also requires both
   endpoints to be Gaussian primes. "Connected component" is the set of primes reachable
   from `z` by `Relation.ReflTransGen (GD D)`; this is the usual connected component for
   the graph on the vertex set of primes.

5. Theorem 1.1 uses `Set.encard` (in `ℕ∞`), with `B : ℕ` cast into `ℕ∞`. An infinite
   component would have `encard = ⊤`, so the bound really says the component is finite
   with at most `B` vertices. This avoids the `Set.ncard` junk value (`ncard` of an
   infinite set is `0`).

6. "Consequently": I read "every sequence of distinct Gaussian primes whose successive
   distances are at most D has at most B_D terms" with finite sequences `Fin n → ℤ[i]`.
   Infinite sequences are not counted: an infinite such sequence is an infinite path, which
   is excluded by the same statement, so the finite version is what is claimed. "Distinct"
   is `Function.Injective`. "Successive distances at most D" is read as
   `gdist (p i) (p (i+1)) ≤ D` for consecutive indices. The bound is the same `B` as in the
   theorem, which depends only on `D`. `B` is chosen before the sequence.

7. Infinite-walk question: an infinite path with no repeated vertex in some `G_D` is an
   injective `ℕ → ℤ[i]` of Gaussian primes with each consecutive pair an edge of `G_D`. The
   answer stated is the negation (no `D`), as the abstract and text say.

8. Not written: the "nonexplicit" and "finite periodic sieve" remarks, and the `D < 1`
   remark (`B_D = 1`), which are not among the three claims the brief lists.
-/

end ReaderC
