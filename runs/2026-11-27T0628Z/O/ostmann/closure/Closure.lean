import Mathlib
import Readings.Ostmann
import ComparatorChallenges.OstmannPrimes

/-! # Target O, family O5 (Ostmann's conjecture): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped. -/

open scoped Pointwise symmDiff

namespace TargetO.Ostmann

theorem two_le_encard {s : Set ℕ} : 2 ≤ s.encard ↔ s.Nontrivial := by
  rw [← Set.one_lt_encard_iff_nontrivial]
  constructor
  · intro h; exact lt_of_lt_of_le (by norm_num) h
  · intro h; exact Order.add_one_le_of_lt h |>.trans_eq' (by norm_num)

theorem sumset_eq (A B : Set ℕ) : {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b} = A + B := by
  ext n; simp only [Set.mem_setOf_eq, Set.mem_add]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩

theorem A_thm : (type_of% @OAI.Ostmann.main) ↔ (type_of% @ReaderA.OstmannReadingA.reading_thm_1_1) := by
  constructor
  · intro h A B hA hB
    have := h A B (two_le_encard.mp hA) (two_le_encard.mp hB)
    show ((ReaderA.OstmannReadingA.sumset A B \ ReaderA.OstmannReadingA.P) ∪
      (ReaderA.OstmannReadingA.P \ ReaderA.OstmannReadingA.sumset A B)).Infinite
    simpa [ReaderA.OstmannReadingA.sumset, ReaderA.OstmannReadingA.P, sumset_eq, symmDiff_def] using this
  · intro h A B hA hB
    have := h A B (two_le_encard.mpr hA) (two_le_encard.mpr hB)
    simpa [ReaderA.OstmannReadingA.symmDiff', ReaderA.OstmannReadingA.sumset,
      ReaderA.OstmannReadingA.P, sumset_eq, symmDiff_def] using this

theorem A_equiv : (type_of% @OAI.Ostmann.main) →
    (type_of% @ReaderA.OstmannReadingA.reading_thm_1_1_equivalently) := by
  intro h Q hQ ⟨A, B, hA, hB, hEq⟩
  have := (A_thm.mp h) A B hA hB
  rw [hEq] at this
  exact this hQ

theorem A_intro : (type_of% @OAI.Ostmann.main) →
    (type_of% @ReaderA.OstmannReadingA.reading_intro_phrasing) := by
  intro h A B hA hB hfin
  have := (A_thm.mp h) A B hA hB
  apply this
  have e : ReaderA.OstmannReadingA.symmDiff' (ReaderA.OstmannReadingA.sumset A B)
      ReaderA.OstmannReadingA.P = ReaderA.OstmannReadingA.symmDiff' ReaderA.OstmannReadingA.P
      (ReaderA.OstmannReadingA.sumset A B) := by
    simp [ReaderA.OstmannReadingA.symmDiff', Set.union_comm]
  rw [e]; exact hfin

theorem B_thm : (type_of% @OAI.Ostmann.main) ↔ (type_of% @ReaderB.reading_ostmann) := by
  constructor
  · intro h A B hA hB
    simpa [ReaderB.sumset, ReaderB.primeSet, sumset_eq] using
      h A B (two_le_encard.mp hA) (two_le_encard.mp hB)
  · intro h A B hA hB
    simpa [ReaderB.sumset, ReaderB.primeSet, sumset_eq] using
      h A B (two_le_encard.mpr hA) (two_le_encard.mpr hB)

theorem B_equiv : (type_of% @OAI.Ostmann.main) → (type_of% @ReaderB.reading_ostmann_equiv) := by
  intro h P hP A B hA hB hEq
  have := (B_thm.mp h) A B hA hB
  rw [hEq] at this; exact this hP

theorem C_thm : (type_of% @OAI.Ostmann.main) ↔ (type_of% @ReaderC.reading_ostmann) := by
  constructor
  · intro h A B hA hB
    simpa [ReaderC.sumset, ReaderC.primeSet, sumset_eq] using
      h A B (two_le_encard.mp hA) (two_le_encard.mp hB)
  · intro h A B hA hB
    simpa [ReaderC.sumset, ReaderC.primeSet, sumset_eq] using
      h A B (two_le_encard.mpr hA) (two_le_encard.mpr hB)

theorem C_equiv : (type_of% @OAI.Ostmann.main) →
    (type_of% @ReaderC.reading_ostmann_equivalently) := by
  intro h S hS A B hA hB hEq
  have := (C_thm.mp h) A B hA hB
  rw [hEq] at this; exact this hS

end TargetO.Ostmann

#print axioms TargetO.Ostmann.A_thm
#print axioms TargetO.Ostmann.A_equiv
#print axioms TargetO.Ostmann.A_intro
#print axioms TargetO.Ostmann.B_thm
#print axioms TargetO.Ostmann.B_equiv
#print axioms TargetO.Ostmann.C_thm
#print axioms TargetO.Ostmann.C_equiv
