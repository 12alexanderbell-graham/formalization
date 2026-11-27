import Mathlib

namespace ReaderA

/-!
# Blind reading (reader A), family O8 "falconer"

Source: `falconer/sources/00_introduction_lines1-25.tex` (Introduction, Theorem 1.1 = `thm:main`).
-/

open MeasureTheory

namespace ReadingA.Falconer

/-- Euclidean distance set `Δ(E) = {|x - y| : x, y ∈ E}` of `E ⊆ ℝ^d`.
`ℝ^d` is `EuclideanSpace ℝ (Fin d)`, whose `dist` is the Euclidean norm `|x - y|`. -/
def distanceSet {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  {t | ∃ x ∈ E, ∃ y ∈ E, t = dist x y}

/-- Theorem 1.1 (`thm:main`): Let `d ≥ 2` be an integer and let `E ⊂ ℝ^d` be compact. If
`dim_H E > d/2`, then `𝓛¹(Δ(E)) > 0`. -/
theorem readingFalconer_main (d : ℕ) (hd : 2 ≤ d) (E : Set (EuclideanSpace ℝ (Fin d)))
    (hE : IsCompact E) (hdim : (d : ENNReal) / 2 < dimH E) :
    0 < volume (distanceSet E) := by
  sorry

end ReadingA.Falconer

/-!
## Ambiguities and choices

1. **ℝ^d** is `EuclideanSpace ℝ (Fin d)` so that `dist x y = |x - y|` is the Euclidean distance
   (on `Fin d → ℝ` Mathlib's `dist` would be the sup distance, which would change `Δ(E)`).
2. **dim_H** is Mathlib's `dimH : Set X → ℝ≥0∞` (Hausdorff dimension w.r.t. the Euclidean
   metric). `d/2` is computed in `ℝ≥0∞` as `(d : ℝ≥0∞) / 2` (division by `2 ≠ 0`, exact, no
   junk); it equals `ENNReal.ofReal (d / 2)`. The strict inequality `>` is kept, as the source
   insists ("The strict threshold is retained, and no endpoint assertion is made").
3. **𝓛¹** is Lebesgue measure on ℝ, Mathlib's `volume : Measure ℝ`. `Δ(E)` is compact (continuous
   image of `E × E`), hence measurable, though `volume` is an outer measure so this is not
   needed for the statement to make sense. Positivity is `0 < volume (distanceSet E)` in `ℝ≥0∞`.
4. `d` is a natural number with `2 ≤ d` ("Let d ≥ 2 be an integer"; d is a dimension, so ℕ).
5. `E` may be empty a priori, but then `dimH E = 0`, so the hypothesis excludes it; no extra
   nonemptiness hypothesis is added.
6. Distance set uses ordered pairs including `x = y` (so `0 ∈ Δ(E)` for nonempty `E`); this
   does not affect positivity of measure.
7. No `sSup`, `tsum`, rpow or ℕ subtraction is used.

## Proved vs stated
* Theorem 1.1 is claimed proved by the source ("We prove this assertion"); the excerpt contains
  only the statement. The surrounding paragraph (no regularity assumptions, positive measure
  rather than dimension one, no endpoint claim) is commentary and is reflected only in choices
  2 and 3 above.
-/
end ReaderA

namespace ReaderB

open MeasureTheory

namespace ReadingO8B

/-- Euclidean distance set Δ(E) = {|x-y| : x,y ∈ E}. -/
def distSet {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, r = dist x y}

/-- Theorem 1.1 (Falconer distance conjecture, all d ≥ 2). dimH takes values in ℝ≥0∞;
ℒ¹ is Lebesgue measure `volume` on ℝ. -/
theorem reading_thm_1_1 (d : ℕ) (hd : 2 ≤ d) (E : Set (EuclideanSpace ℝ (Fin d)))
    (hE : IsCompact E) (hdim : (d : ENNReal) / 2 < dimH E) :
    0 < volume (distSet E) := sorry

end ReadingO8B

/-
Ambiguities / choices (reader B):
* ℝ^d := EuclideanSpace ℝ (Fin d) (so dist is the Euclidean norm |x-y|).
* d/2 is computed in ℝ≥0∞ ((d:ℝ≥0∞)/2), no ℕ division junk; dimH is Mathlib's Hausdorff dimension (ℝ≥0∞).
* ℒ¹(Δ(E)) = Lebesgue (outer) measure `volume` on ℝ; Δ(E) is in fact analytic (continuous image
  of compact E×E), hence measurable, so outer vs measure is immaterial. No sSup/tsum used.
* E empty/small: hypothesis dimH E > d/2 excludes them.
* Proved in source? Theorem 1.1 is the main theorem of the source (excerpt gives statement only).
* Remarks after the theorem (no regularity needed, strict threshold, no endpoint) are not formalized.
-/
end ReaderB

namespace ReaderC

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
end ReaderC
