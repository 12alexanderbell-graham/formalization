import Mathlib

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
