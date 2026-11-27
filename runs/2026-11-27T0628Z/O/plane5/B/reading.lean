import Mathlib

/-- A proper `k`-coloring of the Euclidean plane: any function (no regularity) to `Fin k`
with different colors at distance exactly 1. -/
def IsProperColoring (k : ℕ) (c : EuclideanSpace ℝ (Fin 2) → Fin k) : Prop :=
  ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y

/-- The plane admits a proper `k`-coloring. -/
def PlaneColorable (k : ℕ) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, IsProperColoring k c

/-- Theorem 1.1, first sentence (arbitrary color classes; no measurability). -/
theorem reading_plane_not_five_colorable : ¬ PlaneColorable 5 := sorry

/-- Theorem 1.1, consequence: χ(ℝ²) is the least `k` with `PlaneColorable k`; it exists and
lies in [6,7]. -/
theorem reading_chromatic_number_bounds :
    ∃ m : ℕ, IsLeast {k : ℕ | PlaneColorable k} m ∧ 6 ≤ m ∧ m ≤ 7 := sorry

/- Ambiguities / choices:
* ℝ² = EuclideanSpace ℝ (Fin 2), Euclidean norm; ‖x-y‖=1 rendered as dist x y = 1.
* Colors Fin k (k=0 gives no colorings, harmless). χ(ℝ²) defined as the least element of
  {k | PlaneColorable k}, stated by existence of an IsLeast witness (avoids sInf junk).
* "6 ≤ χ ≤ 7": the source's text says the upper bound 7 is Isbell's hexagonal coloring
  (cited, history; not proved in the excerpt) and the lower bound 4 / 5 are cited (Nelson,
  de Grey 2018 etc.). What the paper proves is "no proper 5-coloring" (hence ≥ 6), working in
  ZFC, using Moser spindle constraints and measurable-data arguments. The theorem as stated
  says "Consequently 6 ≤ χ ≤ 7", so the 7 part is a consequence relying on the cited Isbell
  coloring; my second theorem bundles both.
* The theorem does not need AC/measure; any function allowed (as formalized).
-/
