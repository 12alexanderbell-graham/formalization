import Mathlib

/-!
Blind reading (reader A) of the introduction of
"Logarithmic and Lp Brunn–Minkowski inequalities": Theorem 1.1 and Corollary 1.2.
-/

namespace ReaderA

open MeasureTheory Metric
open scoped Pointwise

/-- The ambient space `ℝ^n`, with its Euclidean inner product and Lebesgue measure `volume`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- "A convex body in `ℝ^n` is a compact convex set with nonempty interior." -/
def IsConvexBody {n : ℕ} (K : Set (Rn n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- Support function `h_K(u) = max_{x ∈ K} ⟨x, u⟩`.  Written as `sSup` of the image of `K`;
for a convex body `K` (compact, nonempty) the image is a nonempty compact subset of `ℝ`, so the
`sSup` is attained, i.e. it is the max.  Only values at `u ∈ S^{n-1}` are ever used. -/
noncomputable def supportFn {n : ℕ} (K : Set (Rn n)) (u : Rn n) : ℝ :=
  sSup ((fun x => inner ℝ x u) '' K)

/-- Wulff body `𝒲[f] = ⋂_{u ∈ S^{n-1}} {x ∈ ℝ^n : ⟨x, u⟩ ≤ f u}`.
`f` is given as a function on all of `ℝ^n`, but only its values on the unit sphere matter. -/
def wulff {n : ℕ} (f : Rn n → ℝ) : Set (Rn n) :=
  ⋂ u ∈ sphere (0 : Rn n) 1, {x | inner ℝ x u ≤ f u}

/-- Theorem 1.1 (even logarithmic Brunn–Minkowski inequality):
`|𝒲[h_K^{1-λ} h_L^λ]| ≥ |K|^{1-λ} |L|^λ`.
The conclusion also records that the left-hand volume is finite, so that `toReal` is faithful. -/
theorem reading_thm_1_1 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L) (hKs : K = -K) (hLs : L = -L)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (wulff (fun u => supportFn K u ^ (1 - t) * supportFn L u ^ t)) ≠ ⊤ ∧
      (volume K).toReal ^ (1 - t) * (volume L).toReal ^ t ≤
        (volume (wulff (fun u => supportFn K u ^ (1 - t) * supportFn L u ^ t))).toReal := by
  sorry

/-- Corollary 1.2 (symmetric `L_p` Brunn–Minkowski inequality), `0 < p < 1`:
`|𝒲[((1-λ) h_K^p + λ h_L^p)^{1/p}]|^{p/n} ≥ (1-λ)|K|^{p/n} + λ|L|^{p/n}`. -/
theorem reading_cor_1_2 (n : ℕ) (hn : 1 ≤ n) (K L : Set (Rn n))
    (hK : IsConvexBody K) (hL : IsConvexBody L) (hKs : K = -K) (hLs : L = -L)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume (wulff (fun u => ((1 - t) * supportFn K u ^ p + t * supportFn L u ^ p) ^ (1 / p)))
        ≠ ⊤ ∧
      (1 - t) * (volume K).toReal ^ (p / n) + t * (volume L).toReal ^ (p / n) ≤
        (volume (wulff (fun u =>
          ((1 - t) * supportFn K u ^ p + t * supportFn L u ^ p) ^ (1 / p)))).toReal ^ (p / n) := by
  sorry

end ReaderA

/-!
## Ambiguities and choices (reader A)

* `ℝ^n` is `EuclideanSpace ℝ (Fin n)`, `⟨x,u⟩` is `inner ℝ x u`, `|K|` is Mathlib's `volume`
  (Lebesgue measure, transported from `Fin n → ℝ`). `S^{n-1}` is `Metric.sphere 0 1`.
* "convex body" = compact ∧ convex ∧ nonempty interior, exactly as the text defines it.
  `K = -K` uses pointwise negation of sets.  In Corollary 1.2, "full-dimensional
  origin-symmetric convex bodies" is read as the same hypotheses (full-dimensional is implied by
  nonempty interior); "origin-symmetric" is read as `K = -K`.
* The parameter `λ` is renamed `t` (`λ` is a Lean keyword); `0 ≤ t ≤ 1` as stated.  `n ≥ 1` is a
  hypothesis as stated.
* Support function: `max` is written as `sSup` of the image `{⟨x,u⟩ : x ∈ K}`.  Junk avoidance:
  under the hypotheses `K` is compact and nonempty, so this set is nonempty and bounded and the
  `sSup` is the attained maximum.  The function is defined on all `u`, but only `u ∈ S^{n-1}`
  enter (the Wulff body only looks at unit `u`).
* Wulff body: defined for any `f : ℝ^n → ℝ` by the displayed intersection over the unit sphere;
  the text's standing assumption "positive continuous function on the sphere" is not imposed in
  the definition.  It holds for the functions actually used (`h_K, h_L > 0` on the sphere for
  origin-symmetric bodies, as the text says), and is not added as a hypothesis since the theorem
  only applies `𝒲` to those functions.
* Real powers: `h_K^{1-λ}`, `h_L^λ`, `h^p`, `(…)^{1/p}` are `Real.rpow`.  Junk avoidance: bases
  are strictly positive on the sphere (support functions of symmetric bodies with nonempty
  interior, and positive combinations of positive powers of them), the only place they are
  evaluated in the Wulff body.  `|K|^{1-λ}`, `|L|^λ`, `|·|^{p/n}` are rpow of real volumes,
  which are strictly positive (nonempty interior).  `p/n` is real division with `n ≥ 1`, so no
  division by zero.
* Volumes: stated with `ENNReal.toReal`.  Junk avoidance: `volume K, volume L < ⊤` because
  compact sets have finite Lebesgue measure (`IsCompact.measure_lt_top`), so no extra hypothesis
  is needed; for the Wulff body the finiteness (`≠ ⊤`) is stated as an explicit conjunct of the
  conclusion (the text asserts the Wulff body is a convex body, hence bounded), so `toReal`
  can never silently turn `⊤` into `0`.
* Inequality direction: written as `rhs ≤ lhs`, equivalent to the text's `lhs ≥ rhs`.
* Corollary 1.2: `|𝒲[…]|^{p/n}` is the real volume raised to the real power `p/n`.
-/
