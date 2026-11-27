import Mathlib
import Readings.SqDiff
import ComparatorChallenges.SquareDifference

/-! # Target O, family O6 (power saving for square-difference-free sets): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped. Direction frozen ⇒
reading for every reading; both directions for reader A (same carrier `Finset ℤ`). -/

namespace TargetO.SqDiff

theorem free_iff_A (A : Finset ℤ) :
    OAI.SquareDifference.IsSquareDifferenceFree A ↔ ReaderA.SqDiffReadingA.SquareDifferenceFree A := by
  unfold OAI.SquareDifference.IsSquareDifferenceFree ReaderA.SqDiffReadingA.SquareDifferenceFree
    ReaderA.SqDiffReadingA.diffSet ReaderA.SqDiffReadingA.posSquares
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h d ⟨⟨a, ha, b, hb, rfl⟩, ⟨m, hm, hd⟩⟩; exact h a ha b hb m hm hd
  · intro h a ha b hb m hm hd; exact h (a - b) ⟨⟨a, ha, b, hb, rfl⟩, ⟨m, hm, hd⟩⟩

theorem A_thm : (type_of% @OAI.SquareDifference.power_saving) ↔
    (type_of% @ReaderA.SqDiffReadingA.reading_thm_1_1) := by
  constructor
  · rintro ⟨c, C, hc, h⟩
    exact ⟨c, C, hc, fun N hN A hA hf => h N hN A hA ((free_iff_A A).mpr hf)⟩
  · rintro ⟨c, C, hc, h⟩
    exact ⟨c, C, hc, fun N hN A hA hf => h N hN A hA ((free_iff_A A).mp hf)⟩

/-- The contrapositive form ("Equivalently …") from the frozen statement, with the same constants. -/
theorem A_equiv : (type_of% @OAI.SquareDifference.power_saving) →
    (type_of% @ReaderA.SqDiffReadingA.reading_thm_1_1_equivalently) := by
  rintro ⟨c, C, hc, h⟩
  refine ⟨c, C, hc, fun N hN A hA hgt => ?_⟩
  by_contra hno
  apply (not_le.mpr hgt) (h N hN A hA _)
  intro a ha b hb m hm hd
  apply hno
  refine ⟨a, ha, b, hb, ?_, m, hm, by rw [hd, abs_of_nonneg (by positivity)]⟩
  intro hab; subst hab; simp at hd; have : (m:ℤ) ^ 2 > 0 := by positivity
  omega

/-- ℕ-carried readings: a `Finset ℕ` in `[1, N]` is carried to `ℤ` by the cast, same cardinality. -/
theorem cast_card (A : Finset ℕ) : (A.map Nat.castEmbedding : Finset ℤ).card = A.card := by simp

theorem cast_sub (N : ℕ) (A : Finset ℕ) (h : A ⊆ Finset.Icc 1 N) :
    (A.map Nat.castEmbedding : Finset ℤ) ⊆ Finset.Icc 1 (N : ℤ) := by
  intro x hx
  simp only [Finset.mem_map, Nat.castEmbedding_apply] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  have := h ha; simp only [Finset.mem_Icc] at this ⊢; omega

theorem B_thm : (type_of% @OAI.SquareDifference.power_saving) →
    (type_of% @ReaderB.reading_sqdiff_bound) := by
  rintro ⟨c, C, hc, h⟩
  refine ⟨c, hc, C, fun N hN A ⟨hA, hf⟩ => ?_⟩
  have := h N hN (A.map Nat.castEmbedding) (cast_sub N A hA) (by
    intro a ha b hb m hm hd
    simp only [Finset.mem_map, Nat.castEmbedding_apply] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨b, hb, rfl⟩ := hb
    exact hf a ha b hb m hm (by
      have h2 : ((a : ℕ) : ℤ) = ((b + m ^ 2 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast h2))
  rwa [cast_card] at this

theorem B_equiv : (type_of% @OAI.SquareDifference.power_saving) →
    (type_of% @ReaderB.reading_sqdiff_equiv) := by
  intro h0
  obtain ⟨c, hc, C, h⟩ := B_thm h0
  refine ⟨c, hc, C, fun N hN A hA hgt => ?_⟩
  by_contra hno
  apply (not_le.mpr hgt) (h N hN A ⟨hA, ?_⟩)
  intro a ha b hb m hm hd
  apply hno
  have hm2 : 0 < m ^ 2 := by positivity
  refine ⟨a, ha, b, hb, by omega, m, hm, ?_⟩
  rw [hd]; push_cast
  rw [show ((b : ℤ) + (m : ℤ) ^ 2 - b) = (m : ℤ) ^ 2 by ring, abs_of_nonneg (sq_nonneg _)]

theorem C_thm : (type_of% @OAI.SquareDifference.power_saving) →
    (type_of% @ReaderC.reading_power_saving) := by
  rintro ⟨c, C, hc, h⟩
  refine ⟨c, hc, C, fun N hN A hA hf => ?_⟩
  have := h N hN (A.map Nat.castEmbedding) (cast_sub N A hA) (by
    intro a ha b hb m hm hd
    simp only [Finset.mem_map, Nat.castEmbedding_apply] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha; obtain ⟨b, hb, rfl⟩ := hb
    exact hf a ha b hb m hm hd)
  rwa [cast_card] at this

theorem C_equiv : (type_of% @OAI.SquareDifference.power_saving) →
    (type_of% @ReaderC.reading_power_saving_equivalently) := by
  intro h0
  obtain ⟨c, hc, C, h⟩ := C_thm h0
  refine ⟨c, hc, C, fun N hN A hA hgt => ?_⟩
  by_contra hno
  apply (not_le.mpr hgt) (h N hN A hA ?_)
  intro a ha b hb m hm hd
  apply hno
  refine ⟨a, ha, b, hb, ?_, m, hm, by rw [hd, abs_of_nonneg (by positivity)]⟩
  intro hab; subst hab; simp at hd; have : (m:ℤ) ^ 2 > 0 := by positivity
  omega

end TargetO.SqDiff

#print axioms TargetO.SqDiff.A_thm
#print axioms TargetO.SqDiff.A_equiv
#print axioms TargetO.SqDiff.B_thm
#print axioms TargetO.SqDiff.B_equiv
#print axioms TargetO.SqDiff.C_thm
#print axioms TargetO.SqDiff.C_equiv
