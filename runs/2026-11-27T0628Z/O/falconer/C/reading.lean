import Mathlib

/-!
Reading C, family O8: "The Falconer distance conjecture in all dimensions".
-/

open MeasureTheory

/-- Theorem 1.1 of the source: for every integer d ≥ 2 and every compact E ⊆ ℝ^d with
`dim_H E > d/2`, the Euclidean distance set Δ(E) = {|x - y| : x, y ∈ E} ⊆ ℝ has positive
one-dimensional Lebesgue measure. -/
theorem reading_thm1 (d : ℕ) (hd : 2 ≤ d) (E : Set (EuclideanSpace ℝ (Fin d)))
    (hE : IsCompact E) (hdim : (d : ENNReal) / 2 < dimH E) :
    0 < (volume : Measure ℝ) {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, r = dist x y} := by
  sorry

/-!
Comments on choices and ambiguities.

* ℝ^d is `EuclideanSpace ℝ (Fin d)`, so `dist` is the Euclidean distance, as the source's
  Δ(E) = {|x - y|} requires.
* The distance set is written inline as `{r | ∃ x ∈ E, ∃ y ∈ E, r = dist x y}`; this is Δ(E)
  exactly as defined in the source.
* ℒ¹ is read as one-dimensional Lebesgue measure on ℝ (`volume` on ℝ), the measure of the
  distance set as a subset of ℝ.
* `dim_H E > d/2` is read strictly, in ℝ≥0∞ with `(d : ℝ≥0∞) / 2`. The source says it makes no
  endpoint assertion, so the non-strict case is not stated.
* The hypothesis `d ≥ 2` is kept. For compact E the sets are nonempty when dim_H E > d/2 > 0,
  so no junk-value case (e.g. of `sSup` on an empty set) arises. Dimension is `dimH` (Hausdorff
  dimension in ℝ≥0∞), so no `sSup`/`tsum` over unbounded or non-summable data is used.
* Proved vs stated: Theorem 1.1 is the paper's main result, stated in the introduction. The
  excerpt I read gives only the introduction (lines 1–25), so the proof is not visible to me.
  The remark that the result needs no regularity, and that Hausdorff dimension one alone
  would not suffice, are commentary and are not stated as theorems here.
* Ambiguity: "or as the source states it" — the source gives the statement with ℒ¹(Δ(E)) > 0
  and no further hypotheses, so no extra hypothesis is added.
-/
