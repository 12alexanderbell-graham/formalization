import Mathlib

/-! # Target O, family propeller: the three blind readings of run 2026-11-27T1428Z (brief 44efa61), concatenated unchanged
apart from the repeated `import Mathlib` lines, so a closure can import them as one module. -/


/-!
Reader A, family O50 (propeller): Theorem 1.1 of "The Gaussian propeller conjecture in
every dimension", read from main.tex lines 36-117 only.
-/

namespace ReaderA

open MeasureTheory Real

/-- `γ_d`: the standard Gaussian measure on `ℝ^d`, written from the source as the measure with
density `(2π)^{-d/2} exp(-‖x‖²/2)` with respect to Lebesgue measure on Euclidean space. -/
noncomputable def gaussianMeasure (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.withDensity fun x =>
    ENNReal.ofReal ((2 * π) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))

/-- The (unnormalized) Gaussian first moment, or "centroid", `z(A) = ∫_A x dγ_d(x)`. -/
noncomputable def centroid (d : ℕ) (A : Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) :=
  ∫ x in A, x ∂(gaussianMeasure d)

/-- `(A_1, …, A_k)` is a measurable partition of `ℝ^d`: measurable cells, pairwise disjoint,
covering the space. Empty cells are allowed. -/
def IsMeasurablePartition {d k : ℕ} (A : Fin k → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧
    (⋃ i, A i) = Set.univ

/-- `𝓕(𝓐) = ∑_{i=1}^k ‖z(A_i)‖²` (Euclidean norm). -/
noncomputable def propellerFunctional {d k : ℕ} (A : Fin k → Set (EuclideanSpace ℝ (Fin d))) :
    ℝ :=
  ∑ i, ‖centroid d (A i)‖ ^ 2

/-- The first two coordinates of `x ∈ ℝ^d` (`d ≥ 2`), viewed as a point of the plane `ℂ`. -/
def planarPart {d : ℕ} (hd : 2 ≤ d) (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ⟨x ⟨0, by omega⟩, x ⟨1, by omega⟩⟩

/-- The propeller partition of `ℝ^d` into `k` cells: three planar sectors of opening angle
`2π/3` (centred at angles `0`, `2π/3`, `-2π/3` in the plane of the first two coordinates),
each multiplied by the orthogonal complement of that plane; every further cell is empty.
With `Complex.arg ∈ (-π, π]` the three sectors are
`(-π/3, π/3]`, `(π/3, π]`, `(-π, -π/3]`. -/
def propeller (d k : ℕ) (hd : 2 ≤ d) : Fin k → Set (EuclideanSpace ℝ (Fin d)) := fun i =>
  if i.val = 0 then
    {x | -(π / 3) < (planarPart hd x).arg ∧ (planarPart hd x).arg ≤ π / 3}
  else if i.val = 1 then
    {x | π / 3 < (planarPart hd x).arg ∧ (planarPart hd x).arg ≤ π}
  else if i.val = 2 then
    {x | -π < (planarPart hd x).arg ∧ (planarPart hd x).arg ≤ -(π / 3)}
  else ∅

/-- Theorem 1.1, inequality. For all positive integers `d, k` and every measurable partition
`(A_1, …, A_k)` of `ℝ^d`: each `x ↦ x` is Bochner-integrable on `A_i` against `γ_d` (so the
centroids are genuine integrals, not the junk value `0`), and
`∑ ‖∫_{A_i} x dγ_d‖² ≤ 9/(8π)`. -/
theorem readingPropellerBound (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (A : Fin k → Set (EuclideanSpace ℝ (Fin d))) (hA : IsMeasurablePartition A) :
    (∀ i, IntegrableOn (fun x => x) (A i) (gaussianMeasure d)) ∧
      propellerFunctional A ≤ 9 / (8 * π) := sorry

/-- Theorem 1.1, sharpness. Whenever `d ≥ 2` and `k ≥ 3`, the propeller (three planar sectors of
angle `2π/3` times the orthogonal complement of their plane, further cells empty) is a
measurable partition of `ℝ^d`, its centroids are genuine integrals, and it attains equality. -/
theorem readingPropellerSharp (d k : ℕ) (hd : 2 ≤ d) (hk : 3 ≤ k) :
    IsMeasurablePartition (propeller d k hd) ∧
      (∀ i, IntegrableOn (fun x => x) (propeller d k hd i) (gaussianMeasure d)) ∧
      propellerFunctional (propeller d k hd) = 9 / (8 * π) := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES

1. Gaussian measure. The source defines `γ_n` by its density `(2π)^{-n/2} exp(-‖x‖²/2)`. I wrote
   it literally as `volume.withDensity` of that density on `EuclideanSpace ℝ (Fin d)` (whose
   `volume` is Lebesgue measure and whose norm is Euclidean), rather than using Mathlib's
   `ProbabilityTheory.stdGaussian`. That it is a probability measure is a fact, not an assumption.
   The real power `(2π)^(-d/2)` has a positive base, so `rpow` has no junk there.

2. Space. `ℝ^d` is `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the Euclidean norm, as the source
   requires ("All norms and inner products below are Euclidean").

3. Centroid. `z(A) = ∫_A x dγ_d(x)` is the Bochner set integral of the identity (vector valued,
   unnormalized, NOT divided by `γ_d(A)`, as the source stresses). Junk value: Mathlib returns `0`
   for a non-integrable integrand. To exclude that, both theorems additionally assert
   `IntegrableOn (fun x => x) (A i) (gaussianMeasure d)` for every cell, so the integrals in the
   statement are genuine. (This is true since the Gaussian has a finite first moment.) No
   division appears anywhere, so no `x/0` junk; no sSup/sInf, no ℕ subtraction, no ℕ∞.

4. Partition. "Measurable partition (A_1,…,A_k)" is read as an indexed family `Fin k → Set`
   with measurable, pairwise disjoint cells whose union is all of `ℝ^d`. Empty cells are allowed
   (nothing forbids `A i = ∅`). The source says partitions are "understood up to Gaussian null
   sets"; I state the theorem for genuine partitions. Since modifying cells on null sets does not
   change any centroid, the a.e.-partition version is equivalent (any a.e. partition can be
   modified on a null set to a genuine one), so this choice loses nothing.

5. `d, k` positive integers: explicit hypotheses `0 < d`, `0 < k` in the bound (for `k = 0`
   there is no partition of a nonempty space; for `d = 0` everything is `0`, so they are
   harmless but kept for literalness).

6. Sharpness sentence. "The constant is sharp whenever d ≥ 2 and k ≥ 3: three planar sectors of
   angle 2π/3, multiplied by the orthogonal complement of their plane, attain equality, with any
   further cells empty." I formalize the specific construction (stronger than a bare existence
   of an attaining partition): the plane is that of the first two coordinates; the sectors are
   cut by `Complex.arg` of `x₀ + i x₁` into `(-π/3, π/3]`, `(π/3, π]`, `(-π, -π/3]`, each of
   opening `2π/3`; membership ignores the other `d-2` coordinates ("multiplied by the orthogonal
   complement"); cells with index ≥ 3 are empty. The boundary rays and the axis `x₀ = x₁ = 0`
   are assigned by the half-open convention of `arg` (with `arg 0 = 0`, so the axis goes to cell
   0); this is a Gaussian null set, consistent with "up to null sets". Any rotation of the
   propeller would do equally; I fixed one. The sharpness theorem asserts the propeller is a
   measurable partition, has integrable cells, and has value exactly `9/(8π)`.

7. Pairwise disjointness is `Pairwise (Disjoint on A)` over distinct indices, so empty cells may
   repeat freely.
-/


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
