import Mathlib

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
