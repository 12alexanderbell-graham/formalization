import Mathlib

namespace ReaderA

open scoped Matrix.Norms.Frobenius

/-- Real 4×4 matrices; the metric used is the Frobenius one (scoped instance opened above). -/
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The trace-one affine hyperplane of `Sym₄(ℝ)`. -/
def TraceOneSym : Set Mat4 := {A : Mat4 | A.IsSymm ∧ A.trace = 1}

/-- `X = {u uᵀ : u ∈ ℝ⁴, ‖u‖ = 1}` (Euclidean norm on `ℝ⁴`). -/
def X : Set Mat4 :=
  {A : Mat4 | ∃ u : EuclideanSpace ℝ (Fin 4), ‖u‖ = 1 ∧ A = Matrix.vecMulVec u u}

/-- `Y` can be covered by `k` subsets of `Y`, each of diameter strictly less than `δ`. -/
def CoverableBy {E : Type*} [PseudoMetricSpace E] (Y : Set E) (k : ℕ) (δ : ℝ) : Prop :=
  ∃ C : Fin k → Set E, (∀ i, C i ⊆ Y) ∧ Y ⊆ ⋃ i, C i ∧ ∀ i, Metric.diam (C i) < δ

/-- Sanity: the Frobenius norm satisfies `‖A‖_F^2 = tr(A^2)` for symmetric `A`, so the
Mathlib metric is the source's metric. (Proved, not part of the claim.) -/
theorem frobenius_sq_eq_trace (A : Mat4) (hA : A.IsSymm) : ‖A‖ ^ 2 = (A * A).trace := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : Matrix.transpose A j i = A j i := by rw [hA.eq]
  rw [Matrix.transpose_apply] at h
  rw [h, sq]

/-- Theorem 1.1. `X` lies in the trace-one hyperplane of `Sym₄(ℝ)`, is compact, has
Frobenius diameter `√2`, and cannot be covered by ten subsets of diameter `< √2`. -/
theorem reading_main :
    X ⊆ TraceOneSym ∧ IsCompact X ∧ Metric.diam X = Real.sqrt 2 ∧
    ¬ CoverableBy X 10 (Real.sqrt 2) := sorry

/-- "Borsuk's assertion fails in dimension nine": some bounded set of positive diameter in
`ℝ⁹` cannot be covered by `9 + 1 = 10` subsets of strictly smaller diameter. -/
theorem reading_dim_nine :
    ∃ Y : Set (EuclideanSpace ℝ (Fin 9)), Bornology.IsBounded Y ∧ 0 < Metric.diam Y ∧
      ¬ CoverableBy Y 10 (Metric.diam Y) := sorry

end ReaderA

/-
Ambiguities and choices (reader A):

1. Ambient space: `Matrix (Fin 4) (Fin 4) ℝ` with Mathlib's Frobenius norm
   (`open scoped Matrix.Norms.Frobenius`), i.e. ‖A‖ = sqrt(Σ |A i j|^2). The source writes
   ‖A‖_F^2 = tr(A^2), which agrees on symmetric matrices (proved as
   `frobenius_sq_eq_trace`; all differences of points of X are symmetric). The diameter is
   the same whether measured in the full matrix space or in the trace-one hyperplane
   (induced metric), so X is kept as a subset of the full matrix space, and
   "⊂ {A ∈ Sym₄ : tr A = 1}" is stated as the conjunct `X ⊆ TraceOneSym`.
2. "‖u‖ = 1": Euclidean norm, `u : EuclideanSpace ℝ (Fin 4)`; `uuᵀ` is
   `Matrix.vecMulVec u u` (entries u i * u j).
3. Compactness: `IsCompact X` in the Frobenius topology (which is the usual product
   topology on matrices).
4. Junk values of `Metric.diam`: it is 0 for unbounded sets. Covering subsets are required
   to be subsets of the set being covered (`C i ⊆ Y`), so they are bounded whenever Y is,
   and no unbounded set can fake diameter 0. In the dimension-nine statement Y is required
   to be bounded explicitly (as in the source's "bounded set"). Empty pieces (diam 0) are
   allowed; this is harmless (equivalent to covering by at most ten pieces).
5. "Covered by ten subsets": `Y ⊆ ⋃ i : Fin 10, C i` with `C i ⊆ Y` (hence equality).
   Covers vs partitions are equivalent per the source; covers are used.
6. Second theorem: "Borsuk's assertion fails in dimension nine" is read as the negation of
   Borsuk's d+1 assertion for d = 9 in `EuclideanSpace ℝ (Fin 9)`: existence of a bounded
   Y with positive diameter not coverable by 10 subsets of strictly smaller diameter. The
   nine-dimensionality of the trace-one hyperplane (needed to transfer Theorem 1.1 to ℝ⁹)
   is not stated separately; the second theorem states the conclusion directly.
-/
