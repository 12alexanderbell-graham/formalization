import Mathlib

open MeasureTheory Metric

namespace ReaderC

/-- The ambient space `ℝ^n` with its Euclidean structure. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A convex body: compact, convex, with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (Rn n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Origin-symmetric: `K = -K`. -/
def IsOriginSymmetric {n : ℕ} (K : Set (Rn n)) : Prop :=
  ∀ x : Rn n, x ∈ K ↔ -x ∈ K

/-- Support function `h_K(u) = max_{x ∈ K} ⟨x, u⟩`, as a supremum of the image. -/
noncomputable def supportFn {n : ℕ} (K : Set (Rn n)) (u : Rn n) : ℝ :=
  sSup ((fun x : Rn n => inner ℝ x u) '' K)

/-- Wulff body `W[f] = ⋂_{u ∈ S^{n-1}} {x : ⟨x, u⟩ ≤ f(u)}`. Only the values of `f`
on the unit sphere are used. -/
def wulff {n : ℕ} (f : Rn n → ℝ) : Set (Rn n) :=
  {x | ∀ u ∈ sphere (0 : Rn n) 1, inner ℝ x u ≤ f u}

/-- Theorem 1.1: the even logarithmic Brunn–Minkowski inequality. -/
theorem reading_theorem_1_1 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : IsOriginSymmetric K) (hLs : IsOriginSymmetric L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume (wulff (fun u => supportFn K u ^ (1 - t) * supportFn L u ^ t))).toReal
      ≥ (volume K).toReal ^ (1 - t) * (volume L).toReal ^ t := sorry

/-- Corollary 1.2: the symmetric `L_p` Brunn–Minkowski inequality for `0 < p < 1`. -/
theorem reading_corollary_1_2 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : IsOriginSymmetric K) (hLs : IsOriginSymmetric L)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume (wulff (fun u =>
        ((1 - t) * supportFn K u ^ p + t * supportFn L u ^ p) ^ (1 / p)))).toReal ^ (p / (n : ℝ))
      ≥ (1 - t) * (volume K).toReal ^ (p / (n : ℝ))
        + t * (volume L).toReal ^ (p / (n : ℝ)) := sorry

/-!
## Ambiguities and choices

1. Parameter name: the text's interpolation parameter `λ` is written `t` (`λ` is a Lean keyword).
2. Ambient space: `ℝ^n` is `EuclideanSpace ℝ (Fin n)`; `n ≥ 1` is the hypothesis `hn`.
   `hn` is unused in the proofs of the statements (it is kept to match the text).
3. Convex body: compact, convex, nonempty interior (the text's definition). Origin-symmetric
   means `x ∈ K ↔ -x ∈ K` (the text's `K = -K`, written elementwise to avoid pointwise
   set-negation instances). With nonempty interior and symmetry, `0` lies in the interior,
   as the text claims; this is not needed as a separate hypothesis.
4. Support function: `h_K(u) = sSup {⟨x,u⟩ : x ∈ K}`. For a nonempty compact set this is a
   maximum, so `sSup` agrees with the text's `max`. No junk value arises because `K` is
   nonempty and bounded. It is evaluated only at unit vectors `u`.
5. Positivity of the base of every real power: for an origin-symmetric convex body and a
   unit vector `u`, `h_K(u) > 0` (the text's claim). So `h_K(u)^(1-t)`, `h_K(u)^p` and
   `(...)^(1/p)` are applied to positive numbers, and `Real.rpow` is the intended power on
   positive reals. The formulas are written for all `u`, but the Wulff body only reads them on
   the unit sphere, so the values off the sphere (where a base could be nonpositive) are unused.
6. Wulff body: the text requires `f` positive and continuous; for `f = h_K^(1-t) h_L^t` (or
   the `L_p` version) this holds, so no extra hypothesis is added. The set
   `{x | ∀ u ∈ sphere 0 1, ⟨x,u⟩ ≤ f u}` is the literal intersection of half-spaces.
7. Volume: Mathlib's `volume` on `EuclideanSpace` is Lebesgue measure, valued in `ℝ≥0∞`.
   I take `.toReal` of both sides, so the statement is real-valued. This is faithful because
   every body involved is finite-volume: `K`, `L` are compact, and the Wulff body is
   contained in a ball (text: it lies inside the ball of radius `max f`), so no `⊤` occurs.
   The `toReal` of `⊤` would be `0`, so the reading relies on this finiteness; it is
   not hidden by any hypothesis.
8. Real powers with base `0`: `volume K`, `volume L` are positive because the bodies have
   nonempty interior, so `0 ^ (1-t)` and `0 ^ t` (with `t = 0` or `1`) never occur. For
   `Real.rpow` with base `0` and exponent `0`, Lean gives `1`, and no such case arises.
9. Corollary 1.2: `full-dimensional` is the nonempty-interior clause of `IsConvexBody`. The
   exponent `p/n` uses `n` cast to `ℝ`, so there is no ℕ subtraction or division.
   `1 - t` is real subtraction, since `t : ℝ`. No ℕ-subtraction junk appears anywhere.
10. Division by `0`: none in the statement except `1 / p` and `p / n`, where `p > 0` and
   `n ≥ 1` (so `(n:ℝ) ≠ 0`) are given.
-/

end ReaderC
