import Mathlib
import Readings.Plane5
import ComparatorChallenges.EuclideanFiveColor
import ComparatorChallenges.PlaneColoring
import Closure.Plane5

/-! # Target O, family O4: the bounds 6 ≤ χ(ℝ²) ≤ 7 from the family's two frozen statements
(run 2026-11-27T0628Z). The family has two comparator challenges: `EuclideanFiveColor` (no proper
five-coloring, on ℂ) and `PlaneColoring` (`properColoring_seven`, on `EuclideanSpace ℝ (Fin 2)`): Isbell's
seven-coloring, which the manuscript cites. Both taken with `type_of%`, never retyped. -/

namespace TargetO.Plane5Bounds

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Colourability in `Fin k` with `dist`, the frozen seven-colouring's form. -/
def Col (k : ℕ) : Prop := ∃ c : Plane → Fin k, ∀ x y : Plane, dist x y = 1 → c x ≠ c y

theorem col_mono {j k : ℕ} (hjk : j ≤ k) (h : Col j) : Col k := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun x => Fin.castLE hjk (c x), fun x y hxy he => hc x y hxy (Fin.castLE_injective hjk he)⟩

theorem not_col_le5 (h5 : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring)) {k : ℕ}
    (hk : k ≤ 5) : ¬ Col k := by
  intro hc
  have := (TargetO.Plane5.C_no_five.mp h5)
  exact this (by obtain ⟨c, hc⟩ := col_mono hk hc; exact ⟨c, hc⟩)

theorem col7 (h7 : (type_of% @OAI.Problem160.properColoring_seven)) : Col 7 := h7

/-- Colourings with colours `Icc 1 k` (reader A) are colourings with `Fin k`. -/
theorem A_iff (k : ℕ) : ReaderA.Plane5ReadingA.ProperlyColorable k ↔ Col k := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun x => ⟨(c x).1 - 1, by have := (c x).2.1; have := (c x).2.2; omega⟩, fun x y hxy he => ?_⟩
    apply hc x y (by rwa [← dist_eq_norm])
    have h1 := (c x).2.1; have h2 := (c y).2.1
    simp only [Fin.mk.injEq] at he
    exact Subtype.ext (by omega)
  · rintro ⟨c, hc⟩
    refine ⟨fun x => ⟨(c x).1 + 1, by constructor <;> omega⟩, fun x y hxy he => ?_⟩
    apply hc x y (by rwa [dist_eq_norm])
    have h3 := congrArg Subtype.val he
    simp only at h3
    exact Fin.ext (by omega)

theorem chi_exists (h5 : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring))
    (h7 : (type_of% @OAI.Problem160.properColoring_seven)) :
    ∃ n : ℕ, Col n ∧ (∀ k < n, ¬ Col k) ∧ 6 ≤ n ∧ n ≤ 7 := by
  classical
  have hex : ∃ n, Col n := ⟨7, col7 h7⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk, ?_, Nat.find_min' hex (col7 h7)⟩
  by_contra hlt; push_neg at hlt
  exact not_col_le5 h5 (by omega) (Nat.find_spec hex)

theorem A_bounds (h5 : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring))
    (h7 : (type_of% @OAI.Problem160.properColoring_seven)) :
    (type_of% @ReaderA.Plane5ReadingA.reading_thm_1_1_bounds) := by
  obtain ⟨n, hn, hmin, h6, h7'⟩ := chi_exists h5 h7
  exact ⟨n, ⟨(A_iff n).mpr hn, fun k hk hc => hmin k hk ((A_iff k).mp hc)⟩, h6, h7'⟩

theorem A_unpacked (h5 : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring))
    (h7 : (type_of% @OAI.Problem160.properColoring_seven)) :
    (type_of% @ReaderA.Plane5ReadingA.reading_thm_1_1_bounds_unpacked) :=
  ⟨fun k hk hc => not_col_le5 h5 hk ((A_iff k).mp hc), ⟨7, le_rfl, (A_iff 7).mpr (col7 h7)⟩⟩

theorem B_bounds (h5 : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring))
    (h7 : (type_of% @OAI.Problem160.properColoring_seven)) :
    (type_of% @ReaderB.reading_chromatic_number_bounds) := by
  obtain ⟨n, hn, hmin, h6, h7'⟩ := chi_exists h5 h7
  refine ⟨n, ⟨hn, fun k hk => ?_⟩, h6, h7'⟩
  by_contra hlt; push_neg at hlt
  exact hmin k hlt hk

theorem C_upper (h7 : (type_of% @OAI.Problem160.properColoring_seven)) :
    (type_of% @ReaderC.reading_chi_upper) := h7

/-- Reader A's graph form, with Mathlib's `chromaticNumber` of the unit-distance graph. -/
theorem A_graph (h5 : (type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring))
    (h7 : (type_of% @OAI.Problem160.properColoring_seven)) :
    (type_of% @ReaderA.Plane5ReadingA.reading_thm_1_1_bounds_graph) := by
  set G := ReaderA.Plane5ReadingA.unitDistanceGraph
  have colG : ∀ k, G.Colorable k ↔ Col k := by
    intro k
    constructor
    · rintro ⟨C⟩
      refine ⟨fun x => C x, fun x y hxy he => ?_⟩
      have hne : x ≠ y := by rintro rfl; simp at hxy
      exact C.valid (by
        simp only [G, ReaderA.Plane5ReadingA.unitDistanceGraph, SimpleGraph.fromRel_adj]
        exact ⟨hne, Or.inl (by rwa [← dist_eq_norm])⟩) he
    · rintro ⟨c, hc⟩
      refine ⟨SimpleGraph.Coloring.mk c fun {x y} hxy => ?_⟩
      simp only [G, ReaderA.Plane5ReadingA.unitDistanceGraph, SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with h | h
      · exact hc x y (by rwa [dist_eq_norm])
      · exact fun he => hc y x (by rwa [dist_eq_norm]) he.symm
  constructor
  · rw [show (6 : ℕ∞) = ((6 : ℕ) : ℕ∞) from rfl, SimpleGraph.le_chromaticNumber_iff_colorable]
    intro m hm
    by_contra hlt
    exact not_col_le5 h5 (by omega) ((colG m).mp hm)
  · exact SimpleGraph.Colorable.chromaticNumber_le ((colG 7).mpr (col7 h7))

end TargetO.Plane5Bounds

#print axioms TargetO.Plane5Bounds.A_bounds
#print axioms TargetO.Plane5Bounds.A_unpacked
#print axioms TargetO.Plane5Bounds.B_bounds
#print axioms TargetO.Plane5Bounds.C_upper
#print axioms TargetO.Plane5Bounds.A_graph
