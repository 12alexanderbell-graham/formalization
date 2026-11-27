import Mathlib
import Readings.Falconer
import ComparatorChallenges.FalconerAllDimensions

/-! # Target O, family O8 (Falconer distance conjecture in all dimensions): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped. -/

open MeasureTheory

namespace TargetO.Falconer

theorem set_eq {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) :
    {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, r = dist x y} = {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} := by
  ext r; simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨x, hx, y, hy, h⟩ <;> exact ⟨x, hx, y, hy, h.symm⟩

theorem A_main : (type_of% @OAI.Falconer.falconer_distance_conjecture) ↔
    (type_of% @ReaderA.ReadingA.Falconer.readingFalconer_main) := by
  constructor
  · intro h d hd E hE hdim
    show 0 < volume {t | ∃ x ∈ E, ∃ y ∈ E, t = dist x y}
    rw [set_eq]; exact h d hd E hE hdim
  · intro h d hd E hE hdim
    have := h d hd E hE hdim
    simpa [ReaderA.ReadingA.Falconer.distanceSet, set_eq] using this

theorem B_main : (type_of% @OAI.Falconer.falconer_distance_conjecture) ↔
    (type_of% @ReaderB.ReadingO8B.reading_thm_1_1) := by
  constructor
  · intro h d hd E hE hdim
    show 0 < volume {r | ∃ x ∈ E, ∃ y ∈ E, r = dist x y}
    rw [set_eq]; exact h d hd E hE hdim
  · intro h d hd E hE hdim
    have := h d hd E hE hdim
    simpa [ReaderB.ReadingO8B.distSet, set_eq] using this

theorem C_main : (type_of% @OAI.Falconer.falconer_distance_conjecture) ↔
    (type_of% @ReaderC.reading_thm1) := by
  constructor
  · intro h d hd E hE hdim
    rw [set_eq]; exact h d hd E hE hdim
  · intro h d hd E hE hdim
    have := h d hd E hE hdim
    rwa [set_eq] at this

end TargetO.Falconer

#print axioms TargetO.Falconer.A_main
#print axioms TargetO.Falconer.B_main
#print axioms TargetO.Falconer.C_main
