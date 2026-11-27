import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

open MeasureTheory Pointwise

/-- The standard inner product `⟨x, y⟩ = ∑ xᵢ yᵢ` on `ℝⁿ = Fin n → ℝ`. -/
def dotR {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- A convex body: a compact convex subset of `ℝⁿ` with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Origin-symmetric: `K = -K`. -/
def IsOriginSymmetric {n : ℕ} (K : Set (Fin n → ℝ)) : Prop := -K = K

/-- The polar body `K° = {y : ⟨x, y⟩ ≤ 1 for every x ∈ K}`. -/
def polarBody {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∀ x ∈ K, dotR x y ≤ 1}

/-- Hanner polytopes, defined recursively:
* a centered nondegenerate interval `[-a, a]`, `a > 0`, is a one-dimensional Hanner polytope;
* if `H₁ ⊂ ℝᵏ`, `H₂ ⊂ ℝˡ` are Hanner polytopes, then `H₁ × H₂` and
  `conv((H₁ × {0}) ∪ ({0} × H₂))` are Hanner polytopes in `ℝ^{k+l}`.
`ℝ^{k+l}` is identified with `ℝᵏ × ℝˡ` via `Fin.append`. -/
inductive IsHanner : (n : ℕ) → Set (Fin n → ℝ) → Prop
  | interval (a : ℝ) (ha : 0 < a) : IsHanner 1 {x | -a ≤ x 0 ∧ x 0 ≤ a}
  | linfSum {k l : ℕ} {H₁ : Set (Fin k → ℝ)} {H₂ : Set (Fin l → ℝ)} :
      IsHanner k H₁ → IsHanner l H₂ →
      IsHanner (k + l) {x | ∃ u ∈ H₁, ∃ v ∈ H₂, x = Fin.append u v}
  | l1Sum {k l : ℕ} {H₁ : Set (Fin k → ℝ)} {H₂ : Set (Fin l → ℝ)} :
      IsHanner k H₁ → IsHanner l H₂ →
      IsHanner (k + l) (convexHull ℝ
        ((fun u => Fin.append u (0 : Fin l → ℝ)) '' H₁ ∪
          (fun v => Fin.append (0 : Fin k → ℝ) v) '' H₂))

/-- A linear Hanner body: an invertible linear image of a Hanner polytope. -/
def IsLinearHannerBody {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∃ T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ), ∃ H : Set (Fin n → ℝ), IsHanner n H ∧ K = T '' H

/-- Theorem 1.1, inequality: `|K| |K°| ≥ 4ⁿ / n!`. Volumes are taken in `ℝ≥0∞`. -/
theorem reading_mahler_inequality (n : ℕ) (hn : 1 ≤ n) (K : Set (Fin n → ℝ))
    (hK : IsConvexBody K) (hsymm : IsOriginSymmetric K) :
    (4 : ENNReal) ^ n / (n.factorial : ENNReal) ≤ volume K * volume (polarBody K) :=
  sorry

/-- Theorem 1.1, equality case: equality holds iff `K` is a linear Hanner body. -/
theorem reading_mahler_equality (n : ℕ) (hn : 1 ≤ n) (K : Set (Fin n → ℝ))
    (hK : IsConvexBody K) (hsymm : IsOriginSymmetric K) :
    volume K * volume (polarBody K) = (4 : ENNReal) ^ n / (n.factorial : ENNReal) ↔
      IsLinearHannerBody K :=
  sorry

end ReaderA

/-
Ambiguities and choices (reader A):

1. Ambient space `ℝⁿ` is `Fin n → ℝ` with its product topology (= Euclidean topology) and
   `volume` = product Lebesgue measure, which is `n`-dimensional Lebesgue volume.
   The inner product `⟨x,y⟩` is written out as `∑ xᵢ yᵢ` (`dotR`), so the polar is literal.
2. Polar body defined exactly as `{y | ∀ x ∈ K, ⟨x,y⟩ ≤ 1}` (one-sided, as in the source),
   not Mathlib's `LinearMap.polar` (which uses `‖⟨x,y⟩‖ ≤ 1`); for symmetric `K` they agree.
3. Junk values avoided: volumes stay in `ℝ≥0∞` (no `toReal`), and `4ⁿ/n!` is computed in
   `ℝ≥0∞` with `n! ≠ 0`, `≠ ∞`, so the division is the honest real quotient. (For a
   symmetric convex body the polar is bounded, so both volumes are finite anyway.)
4. "Origin-symmetric" is `-K = K` (pointwise negation). The source notes that then `0` is
   interior; we do not add this as a hypothesis since it follows.
5. Hanner polytopes: inductive predicate indexed by dimension. The 1-dimensional base case is
   `[-a, a]` with `a > 0` ("centered nondegenerate interval"). The identification
   `ℝ^{k+l} ≅ ℝᵏ × ℝˡ` uses `Fin.append` (first `k` coordinates from `H₁`). The ℓ∞-sum is
   the image of `H₁ × H₂`; the ℓ₁-sum is the convex hull of `(H₁ × {0}) ∪ ({0} × H₂)`.
   Since `k, l` arise from earlier Hanner polytopes they are automatically `≥ 1`.
6. "Linear Hanner body" in `ℝⁿ`: `K = T(H)` with `T` an invertible linear map of `ℝⁿ`
   (a `LinearEquiv`) and `H` an `n`-dimensional Hanner polytope (no translations, consistent
   with "the linear equivalence respects the fixed origin").
7. Theorem 1.1 is split into two theorems (inequality; equality iff linear Hanner body),
   both under the same hypotheses `n ≥ 1`, `K` an origin-symmetric convex body.
-/

-- ===== reader B =====

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

-- ===== reader C =====

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
