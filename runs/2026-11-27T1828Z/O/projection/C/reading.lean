import Mathlib

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
