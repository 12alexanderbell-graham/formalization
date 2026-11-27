import Mathlib
import Readings.Amenable
import ComparatorChallenges.SimpleAmenable

/-! # Target O, family O13 (an infinite finitely presented simple amenable group): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped. Direction frozen ⇒ reading. -/

namespace TargetO.Amenable

theorem fp_of {G : Type} [Group G] (h : Group.IsFinitelyPresented G) :
    ∃ (n : ℕ) (s : Set (FreeGroup (Fin n))), s.Finite ∧
      Nonempty (G ≃* (FreeGroup (Fin n) ⧸ Subgroup.normalClosure s)) :=
  Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup

theorem A_thm : (type_of% @OAI.SimpleAmenable.main) → (type_of% @ReaderA.O13Reading.reading) := by
  rintro ⟨G, hG, hinf, hfp, hs, hfol⟩
  obtain ⟨n, s, hsf, ⟨e⟩⟩ := fp_of hfp
  refine ⟨G, hG, hinf, ⟨Fin n, inferInstance, s, hsf, ⟨e⟩⟩,
    fun N hN => by haveI := hs; haveI := hN; exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N, ?_⟩
  intro K ε hε
  obtain ⟨D, hD, h⟩ := hfol K ε hε
  refine ⟨D, hD, fun g hg => ?_⟩
  convert h g hg

theorem B_thm : (type_of% @OAI.SimpleAmenable.main) → (type_of% @ReaderB.reading) := by
  rintro ⟨G, hG, hinf, hfp, hs, hfol⟩
  obtain ⟨n, s, hsf, ⟨e⟩⟩ := fp_of hfp
  refine ⟨G, hG, hinf, ⟨Fin n, inferInstance, hsf.toFinset, ⟨e.trans (QuotientGroup.quotientMulEquivOfEq (by rw [Set.Finite.coe_toFinset]))⟩⟩, hs, ?_⟩
  intro K ε hε
  obtain ⟨D, hD, h⟩ := hfol K ε hε
  refine ⟨D, hD, fun g hg => ?_⟩
  convert h g hg

theorem C_thm : (type_of% @OAI.SimpleAmenable.main) → (type_of% @ReaderC.reading) := by
  rintro ⟨G, hG, hinf, hfp, hs, hfol⟩
  obtain ⟨n, s, hsf, ⟨e⟩⟩ := fp_of hfp
  refine ⟨G, hG, hinf, fun N hN => by haveI := hs; haveI := hN; exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N, ?_,
    ⟨Fin n, inferInstance, s, hsf, ⟨e⟩⟩⟩
  intro K ε hε
  obtain ⟨D, hD, h⟩ := hfol K ε hε
  refine ⟨D, hD, fun g hg => ?_⟩
  have := h g hg
  convert this using 3
  simp only [ReaderC.leftTranslate, symmDiff_def, Finset.sup_eq_union]

end TargetO.Amenable

#print axioms TargetO.Amenable.A_thm
#print axioms TargetO.Amenable.B_thm
#print axioms TargetO.Amenable.C_thm
