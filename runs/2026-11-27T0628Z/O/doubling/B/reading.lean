import Mathlib

namespace ReaderB

open Metric

/-- `X` is doubling with constant at most `lam`: every (closed) ball is covered by at most `lam`
closed balls of half the radius with centres in `X`. -/
def DoublingAtMost (X : Type*) [MetricSpace X] (lam : ℕ) : Prop :=
  ∀ (x : X) (r : ℝ), 0 < r → ∃ t : Finset X, t.card ≤ lam ∧
    closedBall x r ⊆ ⋃ c ∈ t, closedBall c (r / 2)

/-- bi-Lipschitz embedding with distortion at most `D` into a normed space `F`. -/
def IsBiLipEmbedding {X : Type*} [MetricSpace X] {F : Type*} [NormedAddCommGroup F]
    (f : X → F) (D : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ x y : X, a * dist x y ≤ ‖f x - f y‖ ∧ ‖f x - f y‖ ≤ D * a * dist x y

/-- Real `ℓ₂`. -/
abbrev L2 : Type := lp (fun _ : ℕ => ℝ) 2

/-- Theorem 1.1. -/
theorem readingMain :
    ∃ S : Set L2, DoublingAtMost S 76800 ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (D : ℝ) (f : S → EuclideanSpace ℝ (Fin k)), ¬ IsBiLipEmbedding f D := sorry

/-- Compact obstruction in every infinite-dimensional real Banach space. -/
theorem readingBanach :
    ∃ Λ : ℕ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      ¬ FiniteDimensional ℝ E →
      ∃ K : Set E, IsCompact K ∧ DoublingAtMost K Λ ∧
        ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F], FiniteDimensional ℝ F →
          ∀ (D : ℝ) (f : K → F), ¬ IsBiLipEmbedding f D := sorry

/- AMBIGUITIES AND CHOICES
* Balls: source does not say open/closed. I use closed balls for both the covered ball and the
  covering balls, x ∈ X, r > 0; covering centres lie in X (Finset X, card ≤ λ).
* Doubling of a subset S uses the induced metric on the subtype ↥S.
* Distortion D: any real (finite) D; if D < 1 no embedding exists anyway, so no restriction needed.
  The scale a > 0 is existential, as in the source. Target dimension k ≥ 1 is a nat, finite.
* Target for Theorem 1.1: EuclideanSpace ℝ (Fin k) (ℝ^k with the Euclidean norm, as the source).
* For the Banach statement the target is any finite-dimensional real normed space F (F : Type);
  "universal doubling constant" is `∃ Λ : ℕ` before the quantifier over E. Universe: E, F in `Type`
  (universe 0) to keep the statement a single closed proposition; the source's universality across
  universes is not captured. Λ is not specified numerically (source gives none in the intro).
* "Compact obstruction": K ⊆ E compact set, doubling ≤ Λ, with no bi-Lipschitz embedding into any
  finite-dimensional normed space. Banach space is taken complete (CompleteSpace E), infinite-dimensional
  as ¬ FiniteDimensional ℝ E.
* The source's "isometric realization in L_p" is not formalized (not asked).
-/

end ReaderB
