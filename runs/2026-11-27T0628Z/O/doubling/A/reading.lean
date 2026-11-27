import Mathlib

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
