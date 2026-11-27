import Mathlib

/-! Blind readings A, B, C (code unchanged; only `import Mathlib` hoisted). -/

-- ===== reader A =====

namespace ReaderA

/-- Real `ℓ₂`: square-summable real sequences indexed by `ℕ`, with the Hilbert norm. -/
abbrev ell2 := lp (fun _ : ℕ => ℝ) 2

/-- "`(X, d)` is doubling with constant at most `λ`": every ball in `X` is covered by at most `λ`
balls of half its radius, with centers in `X`. Balls are open balls `B(x, r)`, `r > 0`. -/
def IsDoublingWith (X : Type*) [PseudoMetricSpace X] (lam : ℝ) : Prop :=
  ∀ (x : X) (r : ℝ), 0 < r →
    ∃ t : Finset X, (t.card : ℝ) ≤ lam ∧ Metric.ball x r ⊆ ⋃ y ∈ t, Metric.ball y (r / 2)

/-- "`f : X → V` is a bi-Lipschitz embedding with distortion at most `D`": there is a scale
`a > 0` with `a d(x,y) ≤ ‖f x - f y‖ ≤ D a d(x,y)` for all `x, y ∈ X`. -/
def IsBiLipEmbeddingWith {X V : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup V]
    (f : X → V) (D : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ x y : X, a * dist x y ≤ ‖f x - f y‖ ∧ ‖f x - f y‖ ≤ D * a * dist x y

/-- Theorem 1.1: there is a fixed subset `S` of real `ℓ₂`, with its induced Hilbert distance,
whose doubling constant is at most `76800` and which admits no bi-Lipschitz embedding into `ℝ^k`
for any positive integer `k`, at any finite distortion. -/
theorem reading_thm_1_1 :
    ∃ S : Set ell2, IsDoublingWith S 76800 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ D : ℝ, ∀ f : S → EuclideanSpace ℝ (Fin k),
        ¬ IsBiLipEmbeddingWith f D := sorry

/-- Last paragraph (Section "banach"): in every infinite-dimensional real Banach space there is a
compact obstruction, with a universal doubling constant, admitting no bi-Lipschitz embedding into
any finite-dimensional real normed space. The constant `Λ` is chosen before the space. -/
theorem reading_banach_compact_obstruction :
    ∃ Λ : ℝ, ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y],
      ¬ FiniteDimensional ℝ Y →
        ∃ K : Set Y, IsCompact K ∧ IsDoublingWith K Λ ∧
          ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
            ∀ D : ℝ, ∀ f : K → V, ¬ IsBiLipEmbeddingWith f D := sorry

end ReaderA

/-
Ambiguities and choices (reader A).

1. Real ℓ₂ is `lp (fun _ : ℕ => ℝ) 2` (Mathlib's `ℓ²(ℕ, ℝ)`), whose `dist` is the ℓ²-norm of the
   difference, i.e. the Hilbert distance. `S : Set ell2` coerced to the subtype `↥S` carries the
   induced (subspace) metric, matching "equipped with its induced Hilbert distance".

2. Doubling. "Every ball in X is covered by at most λ balls of half its radius, with centers in X."
   - Open vs closed balls is not specified. I chose open balls `Metric.ball`. (The closed-ball
     version would differ by a bounded change of the constant, but the explicit number 76800 could
     in principle depend on the convention.)
   - "Every ball": radii `r > 0`. For `r ≤ 0` an open ball is empty and the condition is trivial,
     so the restriction is harmless.
   - "Covered by at most λ balls": a finite set `t` of centers in `X` with `card t ≤ λ` and
     `B(x,r) ⊆ ⋃_{y ∈ t} B(y, r/2)`. `λ` is a real number compared with a natural cardinality.
   - "Covered" means covering the ball as a set (the half balls are balls of `X`, centers in `X`).

3. Bi-Lipschitz embedding with distortion at most D: literally `∃ a > 0, ∀ x y,
   a d(x,y) ≤ ‖f x - f y‖ ≤ D a d(x,y)`. Injectivity follows from the lower bound. I define it for
   any (semi)normed target so the same notion serves ℝ^k and general finite-dimensional normed
   spaces.

4. `ℝ^k` with `‖·‖`: chosen as `EuclideanSpace ℝ (Fin k)` (Euclidean norm), since the question is
   about Euclidean spaces. Any norm on ℝ^k would give the same theorem because all norms on ℝ^k
   are equivalent and `D` is arbitrary.

5. "for any positive integer k, at any finite distortion": `∀ k ≥ 1, ∀ D : ℝ, ∀ f, ¬ ...`. Finite
   distortion = real `D` (no `∞`). Negative or small `D` are vacuously excluded, which is fine.

6. Nontriviality / junk: an empty or one-point `S` would trivially be doubling AND embeddable, so
   the non-embeddability clause rules out degenerate witnesses; no extra nonemptiness hypothesis
   needed. "Fixed subset" = one `S` (∃ S before ∀ k, D), not one per `k`.

7. Banach-space statement (from the announcement only; the exact statement of the section is
   not available to me):
   - "every infinite-dimensional real Banach space": `Y` complete real normed space with
     `¬ FiniteDimensional ℝ Y`. Stated for `Y : Type` (universe 0); a universe-polymorphic version
     would let `Λ` depend on the universe level, which is meta-level and irrelevant.
   - "compact obstruction": a compact subset `K ⊆ Y` with the induced metric.
   - "universal doubling constant": a single `Λ` (∃ Λ before ∀ Y). Its value is not given in the
     excerpt, so it is existentially quantified.
   - "no bi-Lipschitz embedding into any finite-dimensional real normed space": for every
     finite-dimensional real normed space `V` (in `Type`), every `D`, every `f : K → V`, `f` is not
     a bi-Lipschitz embedding with distortion ≤ D. This includes `V = 0` and all norms on ℝ^k.
-/

-- ===== reader B =====

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

-- ===== reader C =====

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
