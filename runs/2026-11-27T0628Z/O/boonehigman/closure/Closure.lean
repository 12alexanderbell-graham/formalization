import Mathlib
import Readings.BooneHigman
import ComparatorChallenges.BooneHigman

/-! # Target O, family O32 (the Boone–Higman conjecture): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped (at universe 0): for a finitely generated group G, decidable
word problem (some finite generating family with `ComputablePred` of "the word evaluates to 1") ⇔ G embeds in a
finitely presented (`Group.IsFinitelyPresented`) simple (`IsSimpleGroup`) group of the same universe. Closed
(frozen ⇒ reading): reader B (simple written out: nontrivial, normal subgroups ⊥ or ⊤), reader C (a total
`Computable` Bool decider, `ComputablePred.computable_iff`), reader A's "some generating family" form with G in
`Type` (A's finite presentations: a finite set of relators on `Fin n`, both directions; A's simplicity written out).
Not closed: reader A's "every generating family" form (independence of the generating set is true but is a
computability argument not written here); reader A's statement for G in a higher universe (A puts the simple group
in `Type`). -/

namespace TargetO.BooneHigman

open OAI.FiniteAlgebraicEnvelopes

theorem simple_of {H : Type} [Group H] (h1 : Nontrivial H) (h2 : ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = ⊤) :
    IsSimpleGroup H := by
  refine @IsSimpleGroup.mk H _ h1 ?_
  first
  | exact fun N hN => h2 N hN
  | exact fun N _ => h2 N inferInstance

theorem of_simple {H : Type} [Group H] (h : IsSimpleGroup H) :
    Nontrivial H ∧ ∀ N : Subgroup H, N.Normal → N = ⊥ ∨ N = ⊤ := by
  refine ⟨h.toNontrivial, fun N hN => ?_⟩
  haveI := h; haveI := hN
  first
  | exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N hN
  | exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N

theorem B_thm : (type_of% @OAI.FiniteAlgebraicEnvelopes.main.{0}) →
    (type_of% @ReaderB.reading_boone_higman) := by
  intro h G _ _
  have e := h G
  constructor
  · rintro ⟨n, g, hg, hc⟩
    obtain ⟨H, hH, hfp, hs, f, hf⟩ := e.mp ⟨n, g, hg, hc⟩
    exact ⟨H, hH, hfp, of_simple hs, f, hf⟩
  · rintro ⟨H, hH, hfp, hs, f, hf⟩
    obtain ⟨n, g, hg, hc⟩ := e.mpr ⟨H, hH, hfp, simple_of hs.1 hs.2, f, hf⟩
    exact ⟨n, g, hg, hc⟩

theorem C_thm : (type_of% @OAI.FiniteAlgebraicEnvelopes.main.{0}) →
    (type_of% @ReaderC.reading_boone_higman_thm11) := by
  intro h G _ hG
  have e := h G
  have hw : ∀ {k : ℕ} (g : Fin k → G),
      ReaderC.WordProblemDecidable g ↔ ComputablePred (fun w : Word k => evalWord g w = 1) := by
    intro k g
    rw [ComputablePred.computable_iff]
    constructor
    · rintro ⟨f, hf, hfw⟩
      refine ⟨f, hf, funext fun w => propext ?_⟩
      exact ((hfw w).symm.trans Iff.rfl)
    · rintro ⟨f, hf, hfw⟩
      refine ⟨f, hf, fun w => ?_⟩
      have := congrFun hfw w
      exact (Iff.of_eq this).symm
  constructor
  · rintro ⟨k, g, hg, hd⟩
    exact e.mp ⟨k, g, hg, (hw g).mp hd⟩
  · intro hE
    obtain ⟨k, g, hg, hd⟩ := e.mpr hE
    exact ⟨k, g, hg, (hw g).mpr hd⟩

theorem A_thm : (type_of% @OAI.FiniteAlgebraicEnvelopes.main.{0}) →
    (type_of% @ReaderA.reading_thm_1_1.{0}) := by
  intro h G _ hG
  have hfg : Group.FG G := by
    obtain ⟨n, g, hg⟩ := hG
    exact Group.fg_iff.mpr ⟨Set.range g, hg, Set.finite_range g⟩
  have e := h G
  constructor
  · rintro ⟨n, g, hg, hc⟩
    obtain ⟨H, hH, hfp, hs, f, hf⟩ := e.mp ⟨n, g, hg, hc⟩
    obtain ⟨m, s, hsf, ⟨eq⟩⟩ := (Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup :
      ∃ (n : ℕ) (s : Set (FreeGroup (Fin n))), s.Finite ∧
        Nonempty (H ≃* (FreeGroup (Fin n) ⧸ Subgroup.normalClosure s)))
    refine ⟨H, hH, ⟨m, hsf.toFinset, ⟨eq.trans (QuotientGroup.quotientMulEquivOfEq
      (by rw [Set.Finite.coe_toFinset]))⟩⟩, of_simple hs, f, hf⟩
  · rintro ⟨H, hH, ⟨m, R, ⟨eq⟩⟩, hs, f, hf⟩
    have hfp : Group.IsFinitelyPresented H := Group.IsFinitelyPresented.equiv eq.symm
    obtain ⟨n, g, hg, hc⟩ := e.mpr ⟨H, hH, hfp, simple_of hs.1 hs.2, f, hf⟩
    exact ⟨n, g, hg, hc⟩

end TargetO.BooneHigman

#print axioms TargetO.BooneHigman.A_thm
#print axioms TargetO.BooneHigman.B_thm
#print axioms TargetO.BooneHigman.C_thm
