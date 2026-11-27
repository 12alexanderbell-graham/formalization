import Mathlib

open MeasureTheory

namespace ReaderB

/-- Euclidean space R^n. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A convex body: compact convex with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (E n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- K = -K. -/
def IsOriginSymmetric {n : ℕ} (K : Set (E n)) : Prop := ∀ x ∈ K, -x ∈ K

/-- Polar body. -/
def polar {n : ℕ} (K : Set (E n)) : Set (E n) :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ 1}

/-- Concatenation R^k × R^l → R^(k+l). -/
def append {k l : ℕ} (x : E k) (y : E l) : E (k + l) :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))

/-- ℓ∞ sum: the Cartesian product, placed in R^(k+l). -/
def sumInf {k l : ℕ} (H₁ : Set (E k)) (H₂ : Set (E l)) : Set (E (k + l)) :=
  {z | ∃ x ∈ H₁, ∃ y ∈ H₂, z = append x y}

/-- ℓ1 sum: convex hull of (H₁ × {0}) ∪ ({0} × H₂). -/
def sumOne {k l : ℕ} (H₁ : Set (E k)) (H₂ : Set (E l)) : Set (E (k + l)) :=
  convexHull ℝ ({z | ∃ x ∈ H₁, z = append x 0} ∪ {z | ∃ y ∈ H₂, z = append 0 y})

/-- Hanner polytopes, recursively. -/
inductive IsHanner : (n : ℕ) → Set (E n) → Prop
  | interval (c : ℝ) (hc : 0 < c) : IsHanner 1 {x | ∀ i, |x i| ≤ c}
  | prod {k l : ℕ} {H₁ : Set (E k)} {H₂ : Set (E l)} :
      IsHanner k H₁ → IsHanner l H₂ → IsHanner (k + l) (sumInf H₁ H₂)
  | hull {k l : ℕ} {H₁ : Set (E k)} {H₂ : Set (E l)} :
      IsHanner k H₁ → IsHanner l H₂ → IsHanner (k + l) (sumOne H₁ H₂)

/-- Linear Hanner body: invertible linear image of a Hanner polytope. -/
def IsLinearHanner (n : ℕ) (K : Set (E n)) : Prop :=
  ∃ H : Set (E n), IsHanner n H ∧ ∃ T : E n ≃ₗ[ℝ] E n, K = T '' H

/-- Theorem 1.1, inequality. Volumes are kept in ENNReal (no `toReal`). -/
theorem readingMahlerInequality (n : ℕ) (hn : 1 ≤ n) (K : Set (E n))
    (hK : IsConvexBody K) (hsymm : IsOriginSymmetric K) :
    ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) ≤ volume K * volume (polar K) := sorry

/-- Theorem 1.1, equality case. -/
theorem readingMahlerEquality (n : ℕ) (hn : 1 ≤ n) (K : Set (E n))
    (hK : IsConvexBody K) (hsymm : IsOriginSymmetric K) :
    volume K * volume (polar K) = ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) ↔
      IsLinearHanner n K := sorry

end ReaderB

/-
Ambiguities / choices.
* R^n is EuclideanSpace ℝ (Fin n); |.| is its Lebesgue (Haar) `volume`, inner product the standard one.
* Volumes are ENNReal, so no `toReal` junk; both K and K° are in fact finite for convex bodies
  with symmetric K, so the statement is the intended one. 4^n/n! is cast with ENNReal.ofReal of a real
  division (n! ≠ 0, no ℕ-division).
* "origin-symmetric": ∀ x ∈ K, -x ∈ K (equivalent to K = -K).
* Hanner polytope: base case is the centered interval [-c,c] with c>0 in R^1 (nondegenerate).
  Sums are placed in R^(k+l) via Fin.append (`append`), identifying R^k × R^l with R^(k+l).
  The inductive predicate is indexed by dimension; k,l ≥ 1 is automatic as no Hanner set exists in dim 0.
  ℓ∞ sum = image of product; ℓ1 sum = convex hull of the two coordinate-embedded copies (hull in R^(k+l)).
* Linear Hanner body: image under a linear equiv of E n (fixes the origin, as the source remarks).
* The equality theorem is an iff stated under the same hypotheses; the inequality is a separate theorem.
-/
