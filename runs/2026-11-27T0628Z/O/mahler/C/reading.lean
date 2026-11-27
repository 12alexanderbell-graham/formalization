import Mathlib

open MeasureTheory

namespace ReaderC

/-- Euclidean n-space. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A convex body: compact, convex, nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (E n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Polar body K° = {y : ⟨x,y⟩ ≤ 1 for all x ∈ K}. -/
def polarBody {n : ℕ} (K : Set (E n)) : Set (E n) :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ 1}

/-- Hanner polytopes in coordinates `Fin n → ℝ`, defined recursively:
base case: a centered nondegenerate interval [-a, a] (a > 0) in dimension 1;
closure under the ℓ∞ sum (Cartesian product) and the ℓ1 sum
(convex hull of the two embedded copies, each sitting in its own coordinate block). -/
inductive IsHanner : (n : ℕ) → Set (Fin n → ℝ) → Prop
  | interval {a : ℝ} (ha : 0 < a) : IsHanner 1 {x | x 0 ∈ Set.Icc (-a) a}
  | linf {k l : ℕ} {H₁ : Set (Fin k → ℝ)} {H₂ : Set (Fin l → ℝ)} :
      IsHanner k H₁ → IsHanner l H₂ →
      IsHanner (k + l)
        {x | (fun i : Fin k => x (Fin.castAdd l i)) ∈ H₁ ∧
             (fun j : Fin l => x (Fin.natAdd k j)) ∈ H₂}
  | l1 {k l : ℕ} {H₁ : Set (Fin k → ℝ)} {H₂ : Set (Fin l → ℝ)} :
      IsHanner k H₁ → IsHanner l H₂ →
      IsHanner (k + l)
        (convexHull ℝ
          ({x | (∀ j : Fin l, x (Fin.natAdd k j) = 0) ∧
                 (fun i : Fin k => x (Fin.castAdd l i)) ∈ H₁} ∪
           {x | (∀ i : Fin k, x (Fin.castAdd l i) = 0) ∧
                 (fun j : Fin l => x (Fin.natAdd k j)) ∈ H₂}))

/-- A linear Hanner body: an invertible linear image of a Hanner polytope
(the Hanner polytope is read off through the coordinates `x ↦ (x i)_i`). -/
def IsLinearHanner {n : ℕ} (K : Set (E n)) : Prop :=
  ∃ H : Set (Fin n → ℝ), IsHanner n H ∧
    ∃ T : E n ≃L[ℝ] E n,
      K = (T : E n → E n) '' {x : E n | (fun i : Fin n => x i) ∈ H}

/-- Theorem 1.1, inequality part: for every n ≥ 1 and every origin-symmetric convex body K ⊂ ℝⁿ,
|K| |K°| ≥ 4ⁿ/n!. Stated in ENNReal (both volumes are finite for a convex body, and the
ofReal of the positive constant avoids `toReal`). -/
theorem readingC_mahler_inequality (n : ℕ) (hn : 1 ≤ n) (K : Set (E n))
    (hK : IsConvexBody K) (hsymm : ∀ x : E n, x ∈ K ↔ -x ∈ K) :
    ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) ≤ volume K * volume (polarBody K) :=
  sorry

/-- Theorem 1.1, equality part: for the same K, equality holds iff K is a linear Hanner body. -/
theorem readingC_mahler_equality (n : ℕ) (hn : 1 ≤ n) (K : Set (E n))
    (hK : IsConvexBody K) (hsymm : ∀ x : E n, x ∈ K ↔ -x ∈ K) :
    volume K * volume (polarBody K) = ENNReal.ofReal ((4 : ℝ) ^ n / (n.factorial : ℝ)) ↔
      IsLinearHanner K :=
  sorry

end ReaderC

/-
Ambiguities and choices (reader C):
* Euclidean space is `EuclideanSpace ℝ (Fin n)`; volume is its Mathlib measure (Lebesgue, via the
  inner product space structure); the polar uses the Euclidean inner product `inner ℝ x y`.
* |K||K°| is written in ENNReal: `volume K * volume (polarBody K)` against `ENNReal.ofReal (4^n/n!)`.
  This avoids `toReal` of infinite measures; for a convex body both volumes are finite, so the
  statement is the literal inequality.
* "Origin-symmetric convex body": `IsConvexBody K` (compact, convex, nonempty interior) plus
  `∀ x, x ∈ K ↔ -x ∈ K`. The source notes the origin is interior and fixed; the origin being
  interior follows from symmetry plus nonempty interior and is not separately assumed.
* Hanner polytopes: the source's recursive definition is transcribed as the inductive `IsHanner`
  on subsets of `Fin n → ℝ` (coordinates, so the ℓ∞ and ℓ1 sums can be written with `Fin.castAdd`
  and `Fin.natAdd` instead of a Euclidean product identification). Base case: centered nondegenerate
  interval `[-a, a]`, a > 0. ℓ∞ sum = Cartesian product; ℓ1 sum = convex hull of the union of the
  two embedded copies (each vanishing on the other block).
* Linear Hanner body: K = T(H') where H' is the preimage of a Hanner polytope H under the coordinate
  map x ↦ (x i)_i, and T : E n ≃L[ℝ] E n is an invertible continuous linear map. The source's
  "linear equivalence respects the fixed origin" is automatic since T is linear.
* Equality is stated as an iff under the same hypotheses (n ≥ 1, symmetric convex body).
-/
