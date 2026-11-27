import Mathlib

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
