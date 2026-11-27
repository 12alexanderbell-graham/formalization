import Mathlib

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
