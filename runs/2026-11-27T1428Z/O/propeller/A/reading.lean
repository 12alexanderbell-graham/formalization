import Mathlib

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
