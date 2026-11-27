import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

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

-- ===== reader B =====

namespace ReaderB

open Matrix

abbrev Sym4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Frobenius distance sqrt(tr((A-B)^2)); only used on symmetric matrices. -/
noncomputable def frobDist (A B : Sym4) : ℝ := Real.sqrt (Matrix.trace ((A - B) * (A - B)))

/-- X = {u uᵀ : |u| = 1}. -/
def X : Set Sym4 := {A | ∃ u : Fin 4 → ℝ, ∑ i, u i ^ 2 = 1 ∧ A = Matrix.vecMulVec u u}

/-- Theorem 1.1: compact (Matrix topology = Frobenius topology, finite dim), inside symmetric
trace-one matrices, diameter √2 (all distances ≤ √2 and √2 attained), and no cover by ten
subsets each of diameter < √2. -/
theorem readingBorsukMain :
    IsCompact X ∧ (∀ A ∈ X, A.IsSymm ∧ Matrix.trace A = 1) ∧
    (∀ A ∈ X, ∀ B ∈ X, frobDist A B ≤ Real.sqrt 2) ∧
    (∃ A ∈ X, ∃ B ∈ X, frobDist A B = Real.sqrt 2) ∧
    ¬ ∃ S : Fin 10 → Set Sym4, (∀ i, S i ⊆ X) ∧ X ⊆ ⋃ i, S i ∧
      ∀ i, ∃ r < Real.sqrt 2, ∀ A ∈ S i, ∀ B ∈ S i, frobDist A B ≤ r := sorry

/-- Borsuk's assertion fails in dimension nine. -/
theorem readingBorsukNine :
    ∃ Y : Set (EuclideanSpace ℝ (Fin 9)), Bornology.IsBounded Y ∧ 0 < Metric.diam Y ∧
      ¬ ∃ S : Fin 10 → Set (EuclideanSpace ℝ (Fin 9)), (∀ i, S i ⊆ Y) ∧ Y ⊆ ⋃ i, S i ∧
        ∀ i, Metric.diam (S i) < Metric.diam Y := sorry

/-
Ambiguities / choices:
- Frobenius metric on `Matrix` defined by hand (`frobDist`), as Mathlib has no instance; compactness
  is stated in Matrix's (product) topology, which equals the Frobenius topology.
- "diameter strictly less than √2": ∃ r < √2 bounding all pairwise distances (equals diam < √2;
  empty sets allowed). Pieces are subsets of X.
- "diameter √2": upper bound plus attained value (X compact so sup = max).
- Second theorem: bounded set in EuclideanSpace ℝ (Fin 9), pieces taken as subsets of Y so that
  `Metric.diam` is not a junk 0 on unbounded sets; "smaller diameter" = diam (S i) < diam Y.
  The existence is stated as a bounded Y with positive diameter (compactness not required).
- Real.sqrt of nonnegative values; no junk used (trace of square is ≥ 0).
-/

end ReaderB

-- ===== reader C =====

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
