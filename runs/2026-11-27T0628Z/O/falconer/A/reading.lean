import Mathlib

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
