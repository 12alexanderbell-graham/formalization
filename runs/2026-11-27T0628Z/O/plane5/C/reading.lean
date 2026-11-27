import Mathlib

/-! Reader C, family O4: "The Euclidean plane is not five-colorable" (Theorem 1.1, excerpt lines 1-75). -/

/-- The Euclidean plane ℝ². -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `c : ℝ² → {0,…,k-1}` (i.e. `{1,…,k}` shifted) is a proper coloring: any two points at
unit distance receive different colors. No measurability is imposed on the color classes. -/
def IsProperColoring {k : ℕ} (c : Plane → Fin k) : Prop :=
  ∀ x y : Plane, dist x y = 1 → c x ≠ c y

/-- `k` colors suffice for the plane (no measurability). This replaces the junk-valued
`χ(ℝ²)`: the chromatic number is the least `k` with `Colorable k`, and statements about
`χ` are stated as statements about which `k` are `Colorable`. -/
def Colorable (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k, IsProperColoring c

/-- Theorem 1.1, headline: no proper five-coloring of the plane, arbitrary color classes allowed.
Source: stated as the main theorem; the excerpt gives no proof text beyond the introduction. -/
theorem reading_no_proper_five_coloring : ¬ ∃ c : Plane → Fin 5, IsProperColoring c := sorry

/-- Theorem 1.1, consequence (lower bound): no `k ≤ 5` admits a proper coloring, i.e. `6 ≤ χ(ℝ²)`.
Source: "Consequently, 6 ≤ χ(ℝ²)". -/
theorem reading_chi_lower : ∀ k : ℕ, k < 6 → ¬ Colorable k := sorry

/-- Theorem 1.1, consequence (upper bound): seven colors suffice, i.e. `χ(ℝ²) ≤ 7`.
Source: the excerpt attributes the upper bound seven to Isbell (via the historical record in
Soifer2003History), i.e. it is cited, not proved in the excerpt. -/
theorem reading_chi_upper : Colorable 7 := sorry

/-!
## Ambiguity notes (reader C, O4)

1. Coloring codomain: the source uses `c : ℝ² → {1,…,k}`. I used `Fin k` (0-indexed). This is
   equivalent; no junk values arise (`Fin 0` is empty, and ℝ² is nonempty, so `Colorable 0` is false).
2. Unit distance: the source writes `‖x−y‖ = 1`. I used `dist x y = 1` on `EuclideanSpace ℝ (Fin 2)`,
   which is the Euclidean norm, so the two agree.
3. "Even when arbitrary color classes are allowed": I read this as the absence of any measurability
   hypothesis, so the headline is stated for all functions `c`. The measurable variant `χ_m`
   (Falconer, Payne) is not defined here because the headline does not need it.
4. χ(ℝ²) is not defined as a number. Following the brief, I express "6 ≤ χ ≤ 7" as
   `(∀ k < 6, ¬Colorable k) ∧ Colorable 7`. The lower bound is derived in the source from the
   five-color theorem by monotonicity (a `k`-coloring with `k ≤ 5` gives a 5-coloring); I did not
   formalize that step; `reading_chi_lower` states the consequence directly as a sorry claim.
5. Source boundaries: the excerpt is `introduction_lines1-75.tex`. It ends mid-footnote on the
   Reed2026 manuscript, so the proof of Theorem 1.1 is not in the excerpt. The excerpt cites:
   the upper bound seven (Isbell, via Soifer2003History), the compactness theorem (de Bruijn-Erdős),
   and the measurable/regular-region results (Falconer, Payne, Woodall, Townsend, SokolovVoronov2025).
   None of those are formalized here; the theorem is stated only as the claim.
6. The excerpt mentions a Moser-spindle step "in the final step of our proof"; no proof text is
   in the excerpt, so nothing from it is encoded.
7. The footnote about Reed2026 is a remark about another manuscript; it does not state a claim of
   this paper and is not encoded.
-/
