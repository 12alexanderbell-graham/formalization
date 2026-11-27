import Mathlib

open MeasureTheory Real Complex

namespace ReaderC

noncomputable section

/-- Euclidean space of dimension `d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Standard Gaussian density `(2π)^(-d/2) exp(-‖x‖²/2)`. -/
def gaussDensity (d : ℕ) (x : Euc d) : ℝ :=
  (2 * π) ^ (-(d : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2)

/-- Standard Gaussian probability measure `γ_d` on `ℝ^d`. -/
def gaussMeasure (d : ℕ) : Measure (Euc d) :=
  (volume : Measure (Euc d)).withDensity (fun x => ENNReal.ofReal (gaussDensity d x))

/-- Gaussian first moment (centroid, not normalized) `z(A) = ∫_A x dγ_d(x)`. -/
def centroid (d : ℕ) (A : Set (Euc d)) : Euc d :=
  ∫ x in A, x ∂(gaussMeasure d)

/-- A measurable partition of `ℝ^d` up to Gaussian null sets, with `k` cells
(empty cells allowed). -/
def IsGaussPartition {d k : ℕ} (A : Fin k → Set (Euc d)) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧
  (∀ i j, i ≠ j → gaussMeasure d (A i ∩ A j) = 0) ∧
  gaussMeasure d (⋃ i, A i)ᶜ = 0

/-- The functional `F(A) = ∑ ‖z(A_i)‖²`. -/
def functional {d k : ℕ} (A : Fin k → Set (Euc d)) : ℝ :=
  ∑ i, ‖centroid d (A i)‖ ^ 2

/-- Theorem 1.1, inequality part: `F(A) ≤ 9/(8π)` for every partition, `d, k ≥ 1`. -/
theorem reading_propeller_ineq (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (A : Fin k → Set (Euc d)) (hA : IsGaussPartition A) :
    functional A ≤ 9 / (8 * π) := sorry

/-- Open planar sector of half-opening `π/3` centred at angle `2πj/3`, for a planar point
`a + bi`. The origin is excluded. -/
def sectorCell (j : ℕ) (a b : ℝ) : Prop :=
  (a ≠ 0 ∨ b ≠ 0) ∧
  |Complex.arg ((Complex.mk a b) *
      Complex.exp (((-(2 * π * (j : ℝ) / 3)) : ℝ) : ℂ) * Complex.I)| < π / 3

/-- Theorem 1.1, sharpness part: for `d ≥ 2`, `k ≥ 3` there is a partition attaining equality.
Its first three cells are the three planar sectors of opening `2π/3`, depending only on the first
two coordinates, the other cells are empty. -/
theorem reading_propeller_sharp (d k : ℕ) (hd : 2 ≤ d) (hk : 3 ≤ k) :
    ∃ A : Fin k → Set (Euc d), IsGaussPartition A ∧
      (∀ i : Fin k, 3 ≤ (i : ℕ) → A i = ∅) ∧
      (∀ i : Fin k, (i : ℕ) < 3 → ∀ x : Euc d,
        x ∈ A i ↔ sectorCell (i : ℕ) (x ⟨0, by omega⟩) (x ⟨1, by omega⟩)) ∧
      functional A = 9 / (8 * π) := sorry

end

end ReaderC

/-
Comment block (blind reading C, family O50, source
`propeller/sources/abstract_and_introduction_lines36-117.tex` only).

Modelling choices and ambiguities, all my decisions:

* Euclidean space of dimension `d` is `EuclideanSpace ℝ (Fin d)`, with Mathlib's Lebesgue measure
  `volume` and the Euclidean norm `‖·‖`.
* The standard Gaussian `γ_d` is `volume.withDensity` of `(2π)^(-d/2) exp(-‖x‖²/2)`. The exponent
  `-d/2` is a real rpow exponent, so there is no ℕ subtraction or division.
* The centroid `z(A) = ∫_A x dγ_d(x)` is a Bochner integral. The junk value of a Bochner integral of
  a non-integrable function is `0`. Here `x ↦ x` is `γ_d`-integrable on all of `ℝ^d` (Gaussian moments
  are finite), so for every measurable `A` the value is the genuine first moment. No junk enters.
* "Measurable partition (A_1,…,A_k) of ℝ^d, up to Gaussian null sets, empty cells allowed, cell
  probabilities unrestricted": modelled literally by `IsGaussPartition`. Each cell is measurable,
  distinct cells meet in a `γ_d`-null set, and the complement of the union is `γ_d`-null. Cells need
  not be disjoint or covering on the nose. `F` is insensitive to null modifications, so this is the
  faithful reading of "up to null sets".
* `d, k` positive: `1 ≤ d`, `1 ≤ k`. Cells are indexed by `Fin k`.
* `F(A) = ∑ ‖z(A_i)‖²` is a real sum over a finite index type, so no `ℕ∞` or `⊤` issues arise.
* `9/(8π)` is a real number and `8π ≠ 0`, so no `x/0` issue arises.
* Theorem 1.1 has two parts, given as two theorems. (a) The inequality for all `d, k ≥ 1` and all
  partitions. (b) Sharpness for `d ≥ 2`, `k ≥ 3`: there is a partition attaining equality, with cells
  (i) three planar sectors of opening `2π/3` (centred at directions `0`, `2π/3`, `4π/3`), each
  depending only on coordinates `0` and `1`, which is the "multiplied by the orthogonal complement"
  reading, and (ii) cells of index `≥ 3` empty ("any further cells empty").
* "Attain equality" is read as `F = 9/(8π)` exactly. "The constant is sharp" is read as the existence
  of such a partition, not as a minimality of the constant among all constants.
* Sector model: `sectorCell j a b` holds iff `(a,b) ≠ 0` and `|arg((a+bi)·e^{-2πij/3})| < π/3`. The
  origin and the bounding rays are excluded. They form a Gaussian null set, so the three cells still
  form a partition up to null sets, as required.
* The `by omega` proofs for `⟨0,_⟩`, `⟨1,_⟩` use `2 ≤ d` from `hd`.
* The file has `import Mathlib` only and is wrapped in `namespace ReaderC`. Both theorems are `sorry`.
  It compiles with `lake env lean`, with only the two `sorry` warnings.
-/
