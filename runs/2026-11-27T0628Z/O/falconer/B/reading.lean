import Mathlib

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
