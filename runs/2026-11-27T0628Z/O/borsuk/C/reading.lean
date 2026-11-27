import Mathlib

namespace ReaderC

/-- Real symmetric 4x4 matrices, Sym_4(R). -/
def readingSym4 : Set (Matrix (Fin 4) (Fin 4) ℝ) := {A | A.transpose = A}

/-- The trace-one affine hyperplane of Sym_4(R). -/
def readingT : Set (Matrix (Fin 4) (Fin 4) ℝ) := {A | A ∈ readingSym4 ∧ A.trace = 1}

/-- The Frobenius distance on Sym_4(R): d(A, B) = sqrt(tr((A - B)^2)), i.e. ‖A - B‖_F. -/
noncomputable def readingFrob (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Real.sqrt (Matrix.trace ((A - B) * (A - B)))

/-- X = {uu^T : ‖u‖ = 1}. The Euclidean unit-norm condition is written as `∑ i, u i ^ 2 = 1`. -/
def readingX : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {A | ∃ u : Fin 4 → ℝ, ∑ i, u i ^ 2 = 1 ∧ A = Matrix.of fun i j => u i * u j}

/-- The diameter of a set S in a space with distance function d, as an extended nonnegative real:
sup of d(x, y) over x, y in S. -/
noncomputable def readingEDiam {α : Type*} (d : α → α → ℝ) (S : Set α) : ENNReal :=
  ⨆ x ∈ S, ⨆ y ∈ S, ENNReal.ofReal (d x y)

/-- X is a compact subset of the trace-one hyperplane (default matrix topology, which agrees with
the Frobenius topology). -/
theorem reading_X_compact_in_T : IsCompact readingX ∧ readingX ⊆ readingT := by
  sorry

/-- diam X = sqrt 2 in the Frobenius metric. -/
theorem reading_X_diam : readingEDiam readingFrob readingX = ENNReal.ofReal (Real.sqrt 2) := by
  sorry

/-- X cannot be covered by ten subsets of diameter strictly less than sqrt 2. -/
theorem reading_X_not_ten_cover :
    ¬ ∃ S : Fin 10 → Set (Matrix (Fin 4) (Fin 4) ℝ),
      readingX ⊆ ⋃ i, S i ∧ ∀ i, readingEDiam readingFrob (S i) < ENNReal.ofReal (Real.sqrt 2) := by
  sorry

/-- Second theorem: Borsuk's assertion fails in dimension nine. There is a bounded set Y of
positive diameter in R^9 that cannot be covered by 10 subsets of strictly smaller diameter. -/
theorem reading_dim_nine :
    ∃ Y : Set (EuclideanSpace ℝ (Fin 9)), Bornology.IsBounded Y ∧ 0 < readingEDiam dist Y ∧
      ¬ ∃ S : Fin 10 → Set (EuclideanSpace ℝ (Fin 9)),
        Y ⊆ ⋃ i, S i ∧ ∀ i, readingEDiam dist (S i) < readingEDiam dist Y := by
  sorry

end ReaderC

/-
Ambiguities and choices (comment block):
* Sym_4(R) is `Matrix (Fin 4) (Fin 4) ℝ` restricted to matrices with `transpose = self`.
  The trace-one hyperplane is the subset with trace 1 (Sym ∩ {tr = 1}).
* Frobenius metric: the source gives ‖A‖_F^2 = tr(A^2). I use d(A, B) = sqrt(tr((A - B)^2)), which is
  exactly that norm on A - B. I did not use Mathlib's `Matrix.frobeniusNormedAddCommGroup`, to avoid
  instance clashes.
* "uu^T with ‖u‖ = 1": u ∈ Fin 4 → ℝ with ∑ u_i^2 = 1. This is the Euclidean norm condition written out.
  The matrix uu^T is `Matrix.of (fun i j => u i * u j)`.
* Diameter: `readingEDiam` is the supremum of distances in ENNReal, so an unbounded set has diameter ⊤
  and is never "smaller" than a finite value. This avoids the junk value 0 that a real `sSup` would
  assign to unbounded sets. The empty set has diameter 0.
* "Compact": I wrote IsCompact in the default topology on matrices, which is the Frobenius topology
  (all norms agree in finite dimension).
* "Not coverable by ten subsets of diameter strictly less than sqrt 2": pieces are arbitrary subsets
  of the 4x4 matrix space (indexed by Fin 10, so empty pieces are allowed). Intersecting a piece with X
  would not change the answer, so I did not restrict pieces to subsets of X.
* Second theorem: "some bounded set of positive diameter in R^9" is read literally as bounded, not compact.
  The source's sentence gives a compact set, but the brief's wording is "bounded set". Smaller means
  strictly smaller than diam Y, not a fixed number. The space is `EuclideanSpace ℝ (Fin 9)` with its own `dist`.
-/
