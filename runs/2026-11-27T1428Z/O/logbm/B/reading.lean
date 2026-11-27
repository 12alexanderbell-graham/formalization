import Mathlib

open MeasureTheory

namespace ReaderB

/-- A convex body in `ℝⁿ`: compact, convex, nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Support function `h_K(u) = max_{x ∈ K} ⟨x,u⟩`, written as `sSup` of the image
(for a convex body the image is nonempty, bounded, and the sup is attained). -/
noncomputable def supportFn {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun x => inner ℝ x u) '' K)

/-- Wulff body `⋂_{u ∈ S^{n-1}} {x | ⟨x,u⟩ ≤ f u}`. -/
def wulff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ⋂ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, {x | inner ℝ x u ≤ f u}

/-- Theorem 1.1 (even logarithmic Brunn–Minkowski). Volumes are `(volume ·).toReal`. -/
theorem reading_thm_1_1 (n : ℕ) (hn : 1 ≤ n)
    (K L : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : K = -K) (hLs : L = -L) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (volume K).toReal ^ (1 - lam) * (volume L).toReal ^ lam ≤
      (volume (wulff (fun u => supportFn K u ^ (1 - lam) * supportFn L u ^ lam))).toReal := by
  sorry

/-- Corollary 1.2 (symmetric `L_p` Brunn–Minkowski), `0 < p < 1`. -/
theorem reading_cor_1_2 (n : ℕ) (hn : 1 ≤ n)
    (K L : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (hL : IsConvexBody L)
    (hKs : K = -K) (hLs : L = -L) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    (1 - lam) * (volume K).toReal ^ (p / n) + lam * (volume L).toReal ^ (p / n) ≤
      (volume (wulff (fun u =>
        ((1 - lam) * supportFn K u ^ p + lam * supportFn L u ^ p) ^ (1 / p)))).toReal ^ (p / n) := by
  sorry

/-
Ambiguities and choices.
* Ambient space: `EuclideanSpace ℝ (Fin n)`, with its Lebesgue `volume`; `n ≥ 1` as hypothesis `1 ≤ n`.
* Convex body = compact, convex, nonempty interior (as the text). `K = -K` stated as set equality with
  pointwise negation (`Set.neg`, in scope via `-K`).
* Support function: `sSup` of the image of K; harmless since K is compact nonempty (interior nonempty), so the
  set is nonempty and bounded. Only evaluated on the unit sphere by `wulff`; off the sphere it is irrelevant.
* Wulff body is defined for any `f : E → ℝ`; the text requires f positive continuous on the sphere, which holds
  for f built from symmetric bodies' support functions (positive since 0 is interior); not assumed as hypothesis
  since it is a consequence.
* Real powers: h_K(u), h_L(u) > 0 on the sphere (origin-symmetric body), so rpow of positive reals is fine.
  Off the sphere f is never read. `1/p` fine since p>0. |K|^{..}: volumes of convex bodies are positive and finite
  (compact, nonempty interior), so `toReal` loses nothing; the Wulff body lies in a ball of radius max h, so its
  volume is finite as well, hence `toReal` is faithful there too. In the corollary, `p/n` with n ≥ 1 cast to ℝ,
  no division by zero.
* The Corollary is written with `≤` flipped (RHS ≤ LHS), same as the text's `≥`. The text's "full-dimensional"
  is already part of IsConvexBody (nonempty interior).
* The even log-concave measure part (second half of abstract / Saroglou) is not part of the asked claims.
-/

end ReaderB
