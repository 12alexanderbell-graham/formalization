import Mathlib

namespace ReaderB

open MeasureTheory Real

/-- The standard Gaussian probability measure on `ℝ^d` (as `EuclideanSpace ℝ (Fin d)`),
with density `(2π)^(-d/2) exp(-‖x‖²/2)` with respect to Lebesgue measure. -/
noncomputable def gaussian (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
    (fun x => ENNReal.ofReal ((2 * π) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)))

/-- Gaussian first moment (centroid, unnormalized) `z(A) = ∫_A x dγ_d(x)`. -/
noncomputable def centroid (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) :=
  ∫ x in A, x ∂(gaussian d)

/-- `A : Fin k → Set ℝ^d` is a measurable partition (empty cells allowed). -/
def IsMeasurablePartition {d : ℕ} (k : ℕ) (A : Fin k → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧ (⋃ i, A i) = Set.univ

/-- `F(A) = ∑ᵢ ‖z(Aᵢ)‖²`. -/
noncomputable def functional {d k : ℕ} (A : Fin k → Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  ∑ i, ‖centroid d (A i)‖ ^ 2

/-- Theorem 1.1, inequality. -/
theorem reading_propeller_bound (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (A : Fin k → Set (EuclideanSpace ℝ (Fin d))) (hA : IsMeasurablePartition k A) :
    functional A ≤ 9 / (8 * π) := sorry

/-- The planar sector cells in `ℝ^(n+2)`: the cell `i < 3` consists of the points whose
first two coordinates, read as a complex number, have `arg + π` in
`(i·2π/3, (i+1)·2π/3]` (a sector of opening `2π/3`, the three sectors being centred at
angles `-2π/3, 0, 2π/3`); the factor on the remaining coordinates is the whole of
`ℝ^n`. Cells with index `≥ 3` are empty. -/
def propellerCell (n k : ℕ) (i : Fin k) : Set (EuclideanSpace ℝ (Fin (n + 2))) :=
  {x | (i : ℕ) < 3 ∧
    ((i : ℝ) * (2 * π / 3) < Complex.arg ⟨x 0, x 1⟩ + π ∧
      Complex.arg ⟨x 0, x 1⟩ + π ≤ ((i : ℝ) + 1) * (2 * π / 3))}

/-- Theorem 1.1, sharpness: for `d = n + 2 ≥ 2` and `k ≥ 3`, three planar sectors of
angle `2π/3` times the orthogonal factor (further cells empty) form a measurable partition
attaining `9/(8π)`. -/
theorem reading_propeller_sharp (n k : ℕ) (hk : 3 ≤ k) :
    IsMeasurablePartition k (propellerCell n k) ∧
      functional (propellerCell n k) = 9 / (8 * π) := sorry

/-! ## Comments: ambiguities and choices

* Space: `ℝ^d` is `EuclideanSpace ℝ (Fin d)` so that `‖·‖` is the Euclidean norm. `γ_d` is
  `withDensity` of Lebesgue (`volume`) by the stated density, with `ENNReal.ofReal` (density is
  positive, so no truncation occurs).
* Centroid: Bochner integral `∫ x in A, x ∂γ_d`. Junk value 0 for a non-integrable function is
  avoided in substance: `x` is `γ_d`-integrable on every set (Gaussian has finite first
  moment), so the integral is the genuine one for measurable `A`.
* "Partition up to Gaussian null sets": I take literal measurable partitions
  (measurable, pairwise disjoint, union everything). The functional only depends on the cells
  up to null sets, so nothing is lost for the inequality; for sharpness an honest partition is
  produced. Empty cells allowed, cell probabilities unrestricted (none imposed).
* Indexing: cells are `Fin k → Set`; `d, k` are positive naturals (`0 < d`, `0 < k`
  hypotheses).
* Right-hand side `9 / (8 * π)`: `π > 0`, so no division-by-zero junk.
* Sharpness: stated for `d = n + 2` (all `d ≥ 2`) to have coordinates `0` and `1` without
  casts, and `3 ≤ k`. "Attain equality" is the equation `functional = 9/(8π)` for the explicit
  sector partition, together with it being a measurable partition. Sectors are half-open
  in `arg`, with `arg ∈ (-π, π]`; the origin and boundary rays are null sets and assigned
  to a cell so that the cells genuinely partition. Cells of index `≥ 3` are empty.
* No ℕ subtraction, no `sSup`/`sInf`, no ℕ∞ used.
-/

end ReaderB
