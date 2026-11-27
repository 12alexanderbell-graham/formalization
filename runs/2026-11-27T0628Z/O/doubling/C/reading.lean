import Mathlib

namespace ReaderC

/-- A metric space `X` is doubling with constant at most `lam` if every ball `ball x r` is covered
by at most `lam` balls of radius `r / 2` whose centres lie in `X`. -/
def IsDoublingWith (X : Type*) [MetricSpace X] (lam : ℝ) : Prop :=
  ∀ (x : X) (r : ℝ), ∃ F : Finset X,
    (F.card : ℝ) ≤ lam ∧ Metric.ball x r ⊆ ⋃ y ∈ F, Metric.ball y (r / 2)

/-- `f : X → Y` is a bi-Lipschitz embedding with distortion at most `D` if there is a scale `a > 0`
with `a * d(x, y) ≤ ‖f x - f y‖ ≤ D * a * d(x, y)` for all `x, y`. -/
def IsBiLipschitzWithDistortion {X Y : Type*} [MetricSpace X] [SeminormedAddCommGroup Y]
    (f : X → Y) (D : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ x y : X,
    a * dist x y ≤ ‖f x - f y‖ ∧ ‖f x - f y‖ ≤ D * a * dist x y

/-- Theorem 1.1: a fixed doubling subset of real ℓ₂ with doubling constant at most 76800 and no
bi-Lipschitz embedding into any `ℝ^k`, `k ≥ 1`, at any finite distortion. -/
theorem reading_thm_1_1_hilbert_subset :
    ∃ S : Set (lp (fun _ : ℕ => ℝ) 2),
      IsDoublingWith (↥S) 76800 ∧
      ∀ (k : ℕ), 0 < k → ∀ (f : ↥S → EuclideanSpace ℝ (Fin k)) (D : ℝ),
        ¬ IsBiLipschitzWithDistortion f D := by
  sorry

/-- Second theorem (compact obstruction in every infinite-dimensional real Banach space):
a universal doubling constant `C`, and for each such `E` a compact `K ⊆ E` with doubling constant
at most `C` and no bi-Lipschitz embedding into any finite-dimensional real normed space. -/
theorem reading_thm_compact_banach_obstruction :
    ∃ C : ℝ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      ¬ FiniteDimensional ℝ E →
        ∃ K : Set E, IsCompact K ∧ IsDoublingWith (↥K) C ∧
          ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F], FiniteDimensional ℝ F →
            ∀ (f : ↥K → F) (D : ℝ), ¬ IsBiLipschitzWithDistortion f D := by
  sorry

/-
Ambiguities and choices (doubling family, source lines 31-53 of main.tex):

* Real ℓ₂ is `lp (fun _ : ℕ => ℝ) 2`, with its Hilbert norm and induced metric. A "fixed subset S"
  is `S : Set (lp …)`; it carries the induced metric as the subtype `↥S`.
* "Doubling with constant at most λ": every ball `Metric.ball x r` (x ∈ X, r real) is covered by
  `F : Finset X` with `#F ≤ λ` (as reals) and the balls `Metric.ball y (r/2)`, `y ∈ F`.
  Centres are in X, as the source says. Open balls are used; the source does not say open or
  closed. Radii r ≤ 0 are included (the ball is then empty; no junk effect).
  The constant 76800 is a real number, the bound is `≤`.
* "Bi-Lipschitz embedding with distortion at most D": there is `a > 0` with
  `a d(x,y) ≤ ‖f x - f y‖ ≤ D a d(x,y)`; here `‖·‖` is the norm of the target. The target
  `ℝ^k` is `EuclideanSpace ℝ (Fin k)` (Euclidean norm), `k` a positive integer (`0 < k`).
  Finite distortion: the claim is `∀ D : ℝ, ¬ ...`, i.e. no real D at all. Negative D is also
  covered (it only makes the upper bound harder to satisfy), so this is the strongest reading
  of "at any finite distortion".
* The embedding `f` is an arbitrary function `↥S → ℝ^k`; no continuity or injectivity is assumed
  (injectivity follows from the lower bound with a > 0 when X has distinct points).
* Theorem 1.1 is stated for one fixed S: `∃ S, doubling(≤ 76800) ∧ no embedding`.
* Second theorem (compact obstruction): "universal doubling constant" is read as a single real C
  chosen before E, i.e. `∃ C, ∀ E, ...`. "Real Banach space" is a `NormedAddCommGroup` with
  `NormedSpace ℝ` and `CompleteSpace`. "Infinite-dimensional" is `¬ FiniteDimensional ℝ E`.
  The obstruction is a compact `K : Set E` (`IsCompact K`) whose metric (induced from E) is
  doubling with constant `C`. "No bi-Lipschitz embedding into any finite-dimensional real normed
  space" is: for every finite-dimensional real normed space F (in `Type`) and every `f : ↥K → F`
  and every real `D`, `¬ IsBiLipschitzWithDistortion f D`.
  Universes: E and F are taken in `Type` (universe 0); this is a choice, not a restriction the
  source states.
-/

end ReaderC
