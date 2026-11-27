import Mathlib

/-!
# Readings of family O65 (projection bodies)

Concatenation of the blind readings A, B and C, each unchanged except that its own
`import Mathlib` line is removed.
-/

-- ===== Reader A =====

/-!
# Blind reading A of O65: projection-body inequalities

Paper 1, Theorem 1.1: Petty's projection-volume inequality in every dimension at least four,
with its equality case (affine images of the Euclidean ball).
Paper 2, Theorem 1.1: the exact value of the normalized projection volume of the product of two
ten-dimensional simplices relative to the simplex value, and that it exceeds the simplex value;
Corollary: exponential excess over the simplex, attained by products of simplices.
All definitions (convex body, support function, projection body, normalized projection volume,
the constants) are written from the introductions.
-/

open MeasureTheory Set
open scoped Pointwise

namespace ReaderA

/-- Euclidean space `ℝ^n`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A convex body: compact, convex, with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (E n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Support function `h_L(x) = max_{y ∈ L} ⟨x, y⟩` (used only for documentation of the
projection body below; for compact nonempty `L` the supremum is a maximum). -/
noncomputable def supportFun {n : ℕ} (L : Set (E n)) (x : E n) : ℝ :=
  sSup ((fun y => inner ℝ x y) '' L)

/-- `n`-dimensional volume `|L| = vol_n(L)` (Lebesgue measure of `EuclideanSpace`), as a real
number. Only applied to compact sets, whose volume is finite. -/
noncomputable def vol {n : ℕ} (L : Set (E n)) : ℝ :=
  (volume L).toReal

/-- `vol_{n-1}(proj_{u^⊥} K)`: the Lebesgue measure, inside the hyperplane `u^⊥` (a
finite-dimensional inner product space with its own `volume`), of the orthogonal projection of
`K` onto `u^⊥`. -/
noncomputable def projVol {n : ℕ} (K : Set (E n)) (u : E n) : ℝ :=
  (volume ((Submodule.orthogonalProjectionOnto (ℝ ∙ u)ᗮ) '' K)).toReal

/-- The projection body `Π K`: the convex body whose support function at unit vectors `u` is
`vol_{n-1}(proj_{u^⊥} K)` (extended homogeneously). Written as the set of `x` with
`⟨x, u⟩ ≤ h_{ΠK}(u)` for all unit `u`, which is the unique closed convex set with that support
function (see the comment block). -/
noncomputable def projBody {n : ℕ} (K : Set (E n)) : Set (E n) :=
  {x | ∀ u : E n, ‖u‖ = 1 → inner ℝ x u ≤ projVol K u}

/-- `κ_m = |B_2^m|`, the volume of the Euclidean unit ball in `ℝ^m`. -/
noncomputable def kappa (m : ℕ) : ℝ :=
  vol (Metric.closedBall (0 : E m) 1)

/-- The normalized projection volume `R_n(K) = |Π K| / |K|^{n-1}` (used for `n ≥ 2`). -/
noncomputable def R (n : ℕ) (K : Set (E n)) : ℝ :=
  vol (projBody K) / vol K ^ (n - 1)

/-- The simplex value `c_d = (d+1) d^d / d!`. -/
noncomputable def c (d : ℕ) : ℝ :=
  ((d + 1 : ℝ) * (d : ℝ) ^ d) / (Nat.factorial d : ℝ)

/-- The standard simplex `T_n = conv(0, e_1, …, e_n) ⊂ ℝ^n`. -/
noncomputable def T (n : ℕ) : Set (E n) :=
  convexHull ℝ (insert 0 (range fun i : Fin n => EuclideanSpace.single i (1 : ℝ)))

/-- `K = T_10 × T_10 ⊂ ℝ^20`: a point of `ℝ^20` lies in `K` iff its first ten coordinates form
a point of `T_10` and its last ten coordinates form a point of `T_10`. -/
noncomputable def K20 : Set (E 20) :=
  {x | (EuclideanSpace.equiv (Fin 10) ℝ).symm (fun i => x (Fin.castAdd 10 i)) ∈ T 10 ∧
       (EuclideanSpace.equiv (Fin 10) ℝ).symm (fun i => x (Fin.natAdd 10 i)) ∈ T 10}

/-- A convex polytope: the convex hull of a finite set. -/
def IsPolytope {n : ℕ} (K : Set (E n)) : Prop :=
  ∃ s : Finset (E n), K = convexHull ℝ (s : Set (E n))

/-- Cartesian product of standard simplices on coordinate blocks: for a block assignment
`blk : Fin n → Fin k`, the Minkowski sum over blocks `j` of `conv(0, e_i : blk i = j)`.
Since the blocks use disjoint sets of coordinates, this Minkowski sum is (up to the order of
coordinates) the Cartesian product of the standard simplices of dimensions `|blk⁻¹ j|`. -/
noncomputable def simplexProduct {n k : ℕ} (blk : Fin n → Fin k) : Set (E n) :=
  ∑ j : Fin k,
    convexHull ℝ (insert 0 ((fun i : Fin n => EuclideanSpace.single i (1 : ℝ)) '' {i | blk i = j}))

/-- Paper 1, Theorem 1.1: for every integer `n ≥ 4` and every convex body `K ⊂ ℝ^n`,
`|ΠK| / |K|^{n-1} ≥ κ_{n-1}^n κ_n^{2-n}`, with equality iff `K = a + T B_2^n` for some
`a ∈ ℝ^n` and some invertible linear map `T`. -/
theorem reading_paper1_theorem_1_1 :
    ∀ n : ℕ, 4 ≤ n → ∀ K : Set (E n), IsConvexBody K →
      (vol (projBody K) / vol K ^ (n - 1) ≥ kappa (n - 1) ^ n * kappa n ^ ((2 : ℤ) - n)) ∧
      (vol (projBody K) / vol K ^ (n - 1) = kappa (n - 1) ^ n * kappa n ^ ((2 : ℤ) - n) ↔
        ∃ (a : E n) (Tl : E n ≃ₗ[ℝ] E n),
          K = (fun x => a + Tl x) '' Metric.closedBall (0 : E n) 1) := sorry

/-- Paper 2, Theorem 1.1: for `K = T_10 × T_10 ⊂ ℝ^20`,
`R_20(K)/c_20 = 121 binom(20,10) / (21 · 2^20) = 22355476/22020096 > 1`;
thus `K` violates `|ΠK| ≤ c_20 |K|^19`. -/
theorem reading_paper2_theorem_1_1 :
    R 20 K20 / c 20 = (121 * (Nat.choose 20 10 : ℝ)) / (21 * 2 ^ 20) ∧
    (121 * (Nat.choose 20 10 : ℝ)) / (21 * 2 ^ 20) = (22355476 : ℝ) / 22020096 ∧
    (22355476 : ℝ) / 22020096 > 1 ∧
    ¬ (vol (projBody K20) ≤ c 20 * vol K20 ^ (20 - 1)) := sorry

/-- Paper 2, Corollary (exponential excess): there are `λ > 1` and an integer `N ≥ 20` such
that for every integer `n ≥ N` some full-dimensional convex polytope `K_n ⊂ ℝ^n` satisfies
`R_n(K_n) / R_n(T_n) ≥ λ^n`. -/
theorem reading_paper2_corollary :
    ∃ lam : ℝ, 1 < lam ∧ ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ Kn : Set (E n), IsConvexBody Kn ∧ IsPolytope Kn ∧
        R n Kn / R n (T n) ≥ lam ^ n := sorry

/-- Paper 2, Corollary, with its last sentence: the polytopes `K_n` may be chosen as Cartesian
products of simplices (here: products of standard simplices on coordinate blocks; by affine
invariance of `R_n` this loses nothing against products of arbitrary simplices). -/
theorem reading_paper2_corollary_products :
    ∃ lam : ℝ, 1 < lam ∧ ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ (k : ℕ) (blk : Fin n → Fin k),
        IsConvexBody (simplexProduct blk) ∧ IsPolytope (simplexProduct blk) ∧
        R n (simplexProduct blk) / R n (T n) ≥ lam ^ n := sorry

end ReaderA

/-
AMBIGUITIES AND CHOICES (reader A)

1. Ambient space. `ℝ^n` is `EuclideanSpace ℝ (Fin n)`, with its Lebesgue measure `volume`
   (the one for which the unit cube / an orthonormal parallelepiped has volume 1).
   Coordinates `e_1..e_n` are `EuclideanSpace.single i 1`, `i : Fin n` (indices shifted to
   start at 0).

2. Convex body = compact, convex, nonempty interior (both papers say this; paper 2 adds
   `d ≥ 2`, which holds in every statement used: `n ≥ 4`, `d = 20`, `n ≥ N ≥ 20`).

3. Volumes as reals. `vol L = (volume L).toReal`. `toReal` would turn `∞` into 0 (junk), but
   it is only applied to compact sets (K, ΠK, the unit ball, projections of compact sets under
   a continuous map), which have finite measure. For a convex body `|K| > 0`, so the division
   in `R_n` is not a division by zero; `|ΠK| > 0` as well, so `R_n(T_n) > 0` and the ratio in
   the corollary is genuine.

4. `vol_{n-1}(proj_{u^⊥} K)`. The orthogonal projection is Mathlib's
   `Submodule.orthogonalProjectionOnto (ℝ ∙ u)ᗮ : E n →L[ℝ] (ℝ ∙ u)ᗮ`, and the (n-1)-volume is
   the canonical `volume` of the inner product space `(ℝ ∙ u)ᗮ` (finite dimensional, of
   dimension n-1 for u ≠ 0), i.e. Lebesgue measure normalized by orthonormal bases. I avoided
   Mathlib's Hausdorff measure `μH[n-1]` because it is not normalized to agree with Lebesgue
   measure for the Euclidean metric.

5. Projection body. The text defines ΠK as the (origin-symmetric) convex body whose support
   function at unit `u` is `vol_{n-1}(proj_{u^⊥} K)`, extended homogeneously. I define it as
   `{x | ∀ u, ‖u‖ = 1 → ⟨x,u⟩ ≤ vol_{n-1}(proj_{u^⊥}K)}`. For any closed convex `L`,
   `L = {x | ∀ unit u, ⟨x,u⟩ ≤ h_L(u)}` (separation), so this set IS the body with the stated
   support function, whenever such a body exists (the text takes existence for granted; it is
   the classical Cauchy-formula fact that this function is a support function). `supportFun`
   is defined for documentation; the definition of ΠK does not depend on it.

6. `R_n(K) = |ΠK| / |K|^{n-1}` uses the natural exponent `n - 1` (ℕ subtraction); it is
   only evaluated with `n ≥ 4` or `n ≥ 20`, where no truncation occurs. In paper 1 I wrote the
   ratio explicitly (identical to `R n K`). `κ_n^{2-n}` uses an integer exponent (`zpow`,
   `(2:ℤ) - n`) on `κ_n > 0`, so there is no junk; `κ_{n-1}` uses `n - 1` with `n ≥ 4`.

7. Equality case. "K = a + T B_2^n" with `B_2^n` the closed unit ball (a convex body must be
   compact) and `T` an invertible linear map, written as a linear equivalence
   `E n ≃ₗ[ℝ] E n`. The "≥" and the "iff" are stated for every n ≥ 4 and every convex body.

8. T_10 × T_10 ⊂ ℝ^20: identified with the set of `x ∈ ℝ^20` whose coordinates 0..9 and
   10..19 each form a point of `T_10` (concatenation `ℝ^10 × ℝ^10 ≅ ℝ^20`, which is an
   isometry, so it changes neither volumes nor projection bodies).

9. Theorem 1.1 of paper 2: I state all of: the first equality, the second (pure arithmetic)
   equality, `> 1`, and "K violates the proposed bound", i.e. `¬ (|ΠK| ≤ c_20 |K|^19)`.
   `c_d = (d+1) d^d / d!` is computed in ℝ (`d! > 0`).

10. Corollary of paper 2. `T_n` is read as the standard simplex `conv(0,e_1,…,e_n)` (as in the
   theorem); by affine invariance any simplex gives the same `R_n`. "Full-dimensional convex
   polytope" = convex hull of a finite set with nonempty interior (`IsPolytope` + `IsConvexBody`).
   `λ^n` is a natural power of a real. The last sentence ("may be chosen as Cartesian products
   of simplices") is stated as a separate, stronger version in which `K_n` is a product of
   standard simplices on coordinate blocks, written as a Minkowski sum of faces of the
   coordinate simplex on disjoint coordinate sets (equal to the Cartesian product up to a
   permutation of coordinates, an isometry). Empty blocks contribute `{0}` and are harmless.
   Products of non-standard simplices are affine images of such products, so (by the stated
   affine invariance) nothing is lost.
-/

-- ===== Reader B =====

open MeasureTheory

namespace ReaderB

/-- Euclidean `d`-space. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A convex body: compact, convex, nonempty interior. -/
def IsConvexBody {d : ℕ} (K : Set (E d)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- `vol_{d-1}(proj_{u^⊥} K)`: the Lebesgue measure of the subspace `u^⊥` (the canonical Haar
measure of a finite-dimensional inner product space) of the image of `K` under the orthogonal
projection onto `u^⊥`; as a real number. -/
noncomputable def projVol {d : ℕ} (K : Set (E d)) (u : E d) : ℝ :=
  (volume (((ℝ ∙ u)ᗮ).orthogonalProjectionOnto '' K)).toReal

/-- `P` is the projection body `Π K`: a convex body whose support function `h_P(u) = max_{y ∈ P} ⟪u,y⟫`
equals `vol_{d-1}(proj_{u^⊥} K)` at each unit vector `u`. -/
def IsProjBody {d : ℕ} (K P : Set (E d)) : Prop :=
  IsConvexBody P ∧ ∀ u : E d, ‖u‖ = 1 →
    IsGreatest ((fun y : E d => inner ℝ u y) '' P) (projVol K u)

/-- The normalized functional `R_d(K) = |ΠK| / |K|^{d-1}` for a given body `P` (meant to be `ΠK`). -/
noncomputable def ratio (d : ℕ) (K P : Set (E d)) : ℝ :=
  (volume P).toReal / (volume K).toReal ^ (d - 1)

/-- `κ_m`, the volume of the Euclidean unit ball of `ℝ^m`. -/
noncomputable def kappa (m : ℕ) : ℝ := (volume (Metric.closedBall (0 : E m) 1)).toReal

/-- `c_d = (d+1) d^d / d!`. -/
noncomputable def cConst (d : ℕ) : ℝ := ((d : ℝ) + 1) * (d : ℝ) ^ d / (Nat.factorial d : ℝ)

/-- The simplex `T_d = conv(0, e_1, …, e_d) ⊂ ℝ^d`. -/
def simplex (d : ℕ) : Set (E d) :=
  convexHull ℝ (insert 0 (Set.range fun i : Fin d => EuclideanSpace.single i (1 : ℝ)))

/-- `T_10 × T_10 ⊂ ℝ^20`, with the first ten coordinates and the last ten coordinates. -/
def prodSimplex10 : Set (E 20) :=
  {x | ∃ a ∈ simplex 10, ∃ b ∈ simplex 10, ∀ i : Fin 10,
      x (Fin.castAdd 10 i) = a i ∧ x (Fin.natAdd 10 i) = b i}

/-- Paper 1, Theorem 1.1. -/
theorem readingPetty (n : ℕ) (hn : 4 ≤ n) (K : Set (E n)) (hK : IsConvexBody K) :
    (∃ P, IsProjBody K P) ∧
    ∀ P : Set (E n), IsProjBody K P →
      (kappa (n - 1) ^ n * kappa n ^ ((2 : ℤ) - n) ≤ ratio n K P) ∧
      (ratio n K P = kappa (n - 1) ^ n * kappa n ^ ((2 : ℤ) - n) ↔
        ∃ (a : E n) (T : E n ≃ₗ[ℝ] E n),
          K = (fun x => a + T x) '' Metric.closedBall (0 : E n) 1) := sorry

/-- Paper 2, Theorem 1.1. -/
theorem readingProduct :
    IsConvexBody (prodSimplex10) ∧ (∃ P, IsProjBody prodSimplex10 P) ∧
    ∀ P : Set (E 20), IsProjBody prodSimplex10 P →
      ratio 20 prodSimplex10 P / cConst 20
        = 121 * (Nat.choose 20 10 : ℝ) / (21 * 2 ^ 20) ∧
      (121 * (Nat.choose 20 10 : ℝ) / (21 * 2 ^ 20) = 22355476 / 22020096) ∧
      (1 : ℝ) < ratio 20 prodSimplex10 P / cConst 20 := sorry

/-- Paper 2, Corollary: exponential excess, by products of simplices. -/
theorem readingExponentialExcess :
    ∃ lam : ℝ, 1 < lam ∧ ∃ N : ℕ, 20 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ K : Set (E n), IsConvexBody K ∧
        (∃ s : Finset (E n), K = convexHull ℝ (s : Set (E n))) ∧
        (∃ (m : ℕ) (dim : Fin m → ℕ) (e : (Σ j : Fin m, Fin (dim j)) ≃ Fin n),
          (∀ j, 0 < dim j) ∧
          K = {x | ∀ j : Fin m, ∃ a ∈ simplex (dim j), ∀ i : Fin (dim j), x (e ⟨j, i⟩) = a i}) ∧
        (∃ P, IsProjBody K P) ∧ (∃ Q, IsProjBody (simplex n) Q) ∧
        ∀ P Q : Set (E n), IsProjBody K P → IsProjBody (simplex n) Q →
          lam ^ n ≤ ratio n K P / ratio n (simplex n) Q := sorry

/-
Ambiguities and choices.

* Ambient space: `EuclideanSpace ℝ (Fin d)`, with `volume` its Lebesgue measure (the one giving the
  unit cube measure one); `κ_m` is the volume of the closed unit ball (open ball has the same volume).
* `vol_{d-1}(proj_{u^⊥} K)`: Mathlib's `Measure.hausdorffMeasure` is not normalized to Lebesgue on
  Euclidean spaces, so I used the Haar measure of the finite-dimensional inner product space
  `(ℝ ∙ u)ᗮ` (its `volume`), applied to the image of `K` under `orthogonalProjectionOnto`. The `toReal`
  is harmless since images of compact sets are compact, so the measure is finite. For `u = 0` the
  subspace is everything; this is irrelevant since `projVol` is only constrained at unit vectors.
* Projection body `ΠK`: the text defines it by its support function on the unit sphere (extended
  homogeneously). I did not define a function `ΠK`; I use the predicate `IsProjBody K P` (a convex
  body whose support function `IsGreatest`-max of `⟪u,y⟫` over `P` equals `projVol K u` for all unit `u`).
  The homogeneous extension is automatic for support functions, so only unit `u` are stated. Theorems
  assert existence of such a `P` (the text takes it as given) and then quantify over all such `P`
  (it is unique, since a convex body is determined by its support function).
  The support function is written as `IsGreatest` on the image set (attained maximum) to avoid `sSup`.
  `P` is required to be a convex body (nonempty interior) — a consequence for `K` a convex body,
  which the text asserts ("origin-symmetric convex body").
* `ratio`: `(volume P).toReal / (volume K).toReal ^ (d-1)`. `d - 1` in `ℕ`: only used with `d ≥ 4`
  or `d = 20`, or `n ≥ 20` (and `E n` bodies with nonempty interior have positive volume, so no
  division by zero arises for convex bodies). Likewise `kappa (n - 1)` with `n ≥ 4`, and the
  exponent `2 - n` is an integer (`zpow`) on the positive real `κ_n`.
* Equality case: `K = a + T B_2^n` with `T` an invertible linear map (`≃ₗ`, automatically
  continuous in finite dimension), `B_2^n` the closed unit ball. The "iff" is about `ratio = bound`.
* Paper 2 values: `R_20(K)/c_20` is stated equal to `121·C(20,10)/(21·2^20)` with `Nat.choose`
  cast to `ℝ`, then that fraction equal to `22355476/22020096` (as reals), and `> 1`.
  `T_10 × T_10` is placed in `ℝ^20` as first ten / last ten coordinates (`Fin.castAdd`, `Fin.natAdd`).
  `IsConvexBody prodSimplex10` is included as part of the setting ("let K be…").
* Corollary: `λ > 1` real, `N ≥ 20`; for all `n ≥ N` a convex body `K_n` that is a polytope
  (convex hull of a finite set, nonempty interior from `IsConvexBody`), chosen as a Cartesian
  product of simplices: blocks `j : Fin m` of positive dimension `dim j` summing to `n` via a coordinate
  bijection `e` (any coordinate arrangement; an isometry, so harmless). `R_n(T_n)` uses `simplex n`.
  The inequality is `λ^n ≤ R_n(K)/R_n(T_n)`, with the denominator positive. Existence of `P`, `Q` and
  the universal statement are both given.
* Not formalized: nothing beyond the claims; the "classical contravariance identity" and the
  verification of the simplex value `c_d` (said to be verified in the text) are not stated as claims.
-/

end ReaderB

-- ===== Reader C =====

open MeasureTheory Set

namespace ReaderC

noncomputable section

/-!
# Blind reading C, family O, paper O65: projection bodies

Paper 1: the inequality |ΠK| / |K|^(n-1) ≥ κ_{n-1}^n κ_n^(2-n) for convex bodies in ℝ^n, n ≥ 4,
with the equality case. Paper 2: the exact value of R_20 for T_10 × T_10 divided by c_20, and
an exponential-excess corollary. Definitions follow the introductions only.
-/

/-- Euclidean `n`-space. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `κ_m = |B_2^m|`, the volume of the closed Euclidean unit ball in `ℝ^m`. -/
def kappa (m : ℕ) : ℝ := (volume (Metric.closedBall (0 : E m) 1)).toReal

/-- A convex body: compact, convex, with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (E n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- The unit sphere `S^{n-1}`. -/
def unitSphere (n : ℕ) : Set (E n) := Metric.sphere 0 1

/-- Orthogonal projection onto `u^⊥` for a unit vector `u`. -/
def projPerp {n : ℕ} (u : E n) (x : E n) : E n := x - inner ℝ x u • u

/-- `h_{ΠK}(u) = vol_{n-1}(proj_{u^⊥} K)` for unit `u`. The (n-1)-dimensional volume of a
subset of a hyperplane is taken as `(κ_{n-1} / 2^(n-1)) · μ_H[n-1]`, where `μ_H` is Mathlib's
(unnormalized) Hausdorff measure for the Euclidean metric. -/
def shadowVol {n : ℕ} (K : Set (E n)) (u : E n) : ℝ :=
  kappa (n - 1) / (2 : ℝ) ^ (n - 1) *
    (Measure.hausdorffMeasure ((n : ℝ) - 1) (projPerp u '' K)).toReal

/-- The projection body `ΠK`, the convex body with support function `shadowVol K` on the
sphere. A closed convex set is the intersection of its supporting half-spaces, so
`ΠK = {x | ∀ unit u, ⟪x, u⟫ ≤ h(u)}`. The homogeneous extension of `h` to all of `ℝ^n` gives
the same set, since `⟪x, u⟫ ≤ |u| h(u/|u|)` for all `u` is equivalent to the unit-sphere
condition. -/
def projBody {n : ℕ} (K : Set (E n)) : Set (E n) :=
  {x | ∀ u ∈ unitSphere n, inner ℝ x u ≤ shadowVol K u}

/-- `R_n(K) = |ΠK| / |K|^(n-1)`. -/
def R {n : ℕ} (K : Set (E n)) : ℝ :=
  (volume (projBody K)).toReal / (volume K).toReal ^ (n - 1)

/-- `c_d = (d+1) d^d / d!`. -/
def cD (d : ℕ) : ℝ := ((d : ℝ) + 1) * (d : ℝ) ^ d / (d.factorial : ℝ)

/-- `T_d = conv(0, e_1, …, e_d)` in coordinates. -/
def simplexPi (d : ℕ) : Set (Fin d → ℝ) :=
  convexHull ℝ (insert 0 (Set.range fun i : Fin d => Pi.single i (1 : ℝ)))

/-- The standard simplex `T_d ⊂ E d` as a set in Euclidean space. -/
def simplexE (d : ℕ) : Set (E d) :=
  {x | (fun i : Fin d => x i) ∈ simplexPi d}

/-- `K = T_10 × T_10 ⊂ ℝ^20`, the product of two ten-dimensional simplices. -/
def prodSimplex : Set (E 20) :=
  {x | (fun i : Fin 10 => x (Fin.castAdd 10 i)) ∈ simplexPi 10 ∧
       (fun i : Fin 10 => x (Fin.natAdd 10 i)) ∈ simplexPi 10}

/-- Theorem 1.1 of paper 1 (for every `n ≥ 4` and every convex body): the lower bound with
the equality case `K = a + T B_2^n`, `T` invertible linear. -/
theorem reading_O65_p1_thm11 :
    ∀ n : ℕ, 4 ≤ n → ∀ K : Set (E n), IsConvexBody K →
      (kappa (n - 1) ^ n * kappa n ^ (2 - (n : ℤ)) ≤ R K ∧
        (R K = kappa (n - 1) ^ n * kappa n ^ (2 - (n : ℤ)) ↔
          ∃ (a : E n) (T : E n ≃L[ℝ] E n),
            K = (fun x => a + T x) '' Metric.closedBall 0 1)) := by
  sorry

/-- Theorem 1.1 of paper 2: `R_20(K)/c_20` for `K = T_10 × T_10` is exactly
`121 · C(20,10) / (21 · 2^20) = 22355476 / 22020096`, and this exceeds one. -/
theorem reading_O65_p2_thm11 :
    R prodSimplex / cD 20 = 121 * (Nat.choose 20 10 : ℝ) / (21 * (2 : ℝ) ^ 20) ∧
    R prodSimplex / cD 20 = (22355476 : ℝ) / 22020096 ∧
    1 < R prodSimplex / cD 20 := by
  sorry

/-- Corollary of paper 2: there are `λ > 1` and `N ≥ 20` such that for every `n ≥ N` some
full-dimensional convex polytope `K_n ⊂ ℝ^n` has `R_n(K_n)/R_n(T_n) ≥ λ^n`. -/
theorem reading_O65_p2_cor :
    ∃ lam : ℝ, 1 < lam ∧ ∃ N : ℕ, 20 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        ∃ K : Set (E n), IsConvexBody K ∧
          (∃ S : Finset (E n), K = convexHull ℝ (S : Set (E n))) ∧
          lam ^ n ≤ R K / R (simplexE n) := by
  sorry

/-!
## Ambiguities and choices (reader C, O65)

1. Projection body. Defined as the set `{x | ∀ unit u, ⟪x,u⟫ ≤ h(u)}` with `h(u)` the
   (unit-sphere) shadow volume, since the text defines `ΠK` by its support function and
   `ΠK` is the closed convex set with that support function. The homogeneous extension to
   all of ℝ^n is not written out; the unit-sphere condition gives the same set (comment in
   `projBody`).
2. Volume of shadows. The text uses the (n-1)-volume on the hyperplane `u^⊥`. Mathlib has no
   direct hyperplane volume. I used kappa of dimension n-1, times the power of two with
   exponent n-1 in the denominator, times the Hausdorff measure of dimension n-1, on `E n`, where `μ_H` is
   Mathlib's unnormalized Hausdorff measure. This is a standard identity (Lebesgue measure on
   a k-plane is kappa_k times two to the minus k, times the unnormalized Hausdorff measure of dimension k for the
   Euclidean metric) but I did not verify the constant in Mathlib, so it is a choice that may
   need checking. The shadow is compact for compact `K`, so its measure is finite.
3. Orthogonal projection. `projPerp u x = x - ⟪x,u⟫ u` for unit `u`, the orthogonal projection
   onto `u^⊥`. Defined only for unit `u`, which is the only case used.
4. Convex body. Compact, convex, nonempty interior (as stated in the text). `|K| > 0` for
   convex bodies, so the division in `R` has no zero-denominator junk; `R` for non-bodies is
   not used.
5. Natural-number subtraction. `n - 1` appears in `kappa (n-1)`, `2^(n-1)`, `R`, and the
   Hausdorff dimension `(n : ℝ) - 1`. Every use is with `n ≥ 4` (or `n ≥ 20`), so the
   subtraction is genuine. The exponent `2 - n` of `κ_n` is an integer power (ℤ), so there
   is no ℕ subtraction; `κ_n > 0` so `zpow` has no zero-base junk.
6. Equality case. Stated as: `R K = bound` iff `K = a + T B_2^n` for some `a : E n` and
   `T : E n ≃L[ℝ] E n` (invertible linear), with `B_2^n` the closed unit ball. The text says
   "for all convex bodies"; the equality clause is inside the `∀ K`.
7. `c_d` and `R` on the product. `c_20` is `cD 20`, which has the form twenty-one times
   twenty to the twentieth, all over twenty factorial, as a real division (twenty factorial is
   positive). The text's exact closed form uses the binomial coefficient `Nat.choose 20 10`
   with the factor 121 and the denominator 21 times 2 to the 20th. The displayed numeric
   value 22355476 over 22020096 is written as a literal real division; both forms are asserted
   equal to the ratio.
8. The simplex. `T_d = conv(0, e_1, …, e_d)`; `simplexPi` is in `Fin d → ℝ` (affine-invariant
   data only), `simplexE` pulls it back to `E d` by the coordinate map. Convex hull is an
   affine notion, so the choice of Euclidean versus coordinate ambient does not matter.
9. Product. `prodSimplex` is `{x ∈ ℝ^20 | first 10 coordinates ∈ T_10 and last 10 ∈ T_10}`,
   which is `T_10 × T_10` under the identification `ℝ^20 = ℝ^10 × ℝ^10`. `Fin.castAdd`/`Fin.natAdd`
   realize the two blocks. The claim that `prodSimplex` is a convex body (needed for the text
   to call it a body) is not written as a conjunct; it is implicit in the product of bodies.
10. Corollary. `R_n(T_n)` is written as `R (simplexE n)` (the simplex itself, not `c_n`). The
   full-dimensional polytope condition is `IsConvexBody` plus `K` the convex hull of a finite set.
   Not formalized: the final sentence "the polytopes may be chosen as Cartesian products of
   simplices", since that requires a formal notion of a product of simplices of varying
   dimensions summing to `n`; I did not write it. It is a permissive "may", not part of the
   bound.
11. Mathlib names used: `inner ℝ`, `Measure.hausdorffMeasure`, `volume` on `EuclideanSpace`,
   `Metric.closedBall`, `Metric.sphere`, `convexHull`, `Pi.single`, `Fin.castAdd`, `Fin.natAdd`,
   `ContinuousLinearEquiv`.
-/

end

end ReaderC

