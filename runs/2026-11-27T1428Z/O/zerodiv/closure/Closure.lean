import Mathlib
import Readings.zerodiv
import ComparatorChallenges.TorsionFreeZeroDivisors

/-! # Target O, family O45 (Kaplansky's zero-divisor conjecture): closures (run 2026-11-27T1428Z).
Frozen statement `MainTheorem` (the challenge's own conjunction of Theorem 1.1 with its "Moreover" clause),
taken by name, never retyped. Closed from it: every reader's first sentence of Theorem 1.1 (3/3), every reader's
"Kaplansky's conjecture is false" (3/3), and reader B's "Moreover" and full Theorem 1.1 (its classifying space:
a path-connected finite CW complex of dimension at most two with a contractible covering space and the right
fundamental group). Reader C's torsion-freeness (`IsMulTorsionFree`, Mathlib's commuting-roots form) is proved
equivalent to the frozen one for groups. Readers A's and C's classifying spaces are not closed: A asks for the
higher homotopy groups to vanish and C for a simplicial complex; deriving either from the frozen "contractible
covering space of a finite CW complex" needs theory Mathlib lacks (lifting homotopy groups through covering
maps; triangulating CW complexes). -/

namespace TargetO.ZeroDiv

open OAI.TorsionFreeZeroDivisors

theorem tf_iff_mulTorsionFree (G : Type) [Group G] : TorsionFree G ↔ IsMulTorsionFree G := by
  constructor
  · intro h
    refine ⟨fun n hn a b hab he => ?_⟩
    have h1 : (a * b⁻¹) ^ n = 1 := by
      rw [(hab.inv_right).mul_pow, inv_pow, he, mul_inv_cancel]
    exact mul_inv_eq_one.1 (h _ n (Nat.pos_of_ne_zero hn) h1)
  · intro h g n hn hg
    have : g ^ n = (1 : G) ^ n := by rw [hg, one_pow]
    exact IsMulTorsionFree.pow_left_injective (Nat.pos_iff_ne_zero.1 hn) (Commute.one_right g) this

theorem tf_iff_B (G : Type) [Group G] : TorsionFree G ↔ ReaderB.TorsionFreeGroup G := by
  constructor
  · intro h g hg hfin
    obtain ⟨n, hn, hgn⟩ := hfin.exists_pow_eq_one
    exact hg (h g n hn hgn)
  · intro h g n hn hgn
    by_contra hg
    exact h g hg (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hgn⟩)

theorem fp_B (G : Type) [Group G] (h : Group.IsFinitelyPresented G) : ReaderB.FinitelyPresentedGroup G := by
  obtain ⟨n, φ, hφ, S, hS, hker⟩ := h.out
  exact ⟨n, S, hS, ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩⟩

/-! First sentence of Theorem 1.1. -/

theorem A_thm (H : MainTheorem) : type_of% @ReaderA.reading_thm_1_1 := by
  obtain ⟨G, _, hfp, htf, -, α, β, hα, hβ, h⟩ := H
  exact ⟨G, _, hfp, htf, α, β, hα, hβ, h⟩

theorem B_thm (H : MainTheorem) : type_of% @ReaderB.reading_zerodiv_main := by
  obtain ⟨G, _, hfp, htf, -, α, β, hα, hβ, h⟩ := H
  exact ⟨G, _, fp_B G hfp, (tf_iff_B G).1 htf, α, β, hα, hβ, h⟩

theorem C_thm (H : MainTheorem) : type_of% @ReaderC.reading_zerodiv_thm1_1_part1 := by
  obtain ⟨G, _, hfp, htf, -, α, β, hα, hβ, h⟩ := H
  exact ⟨G, _, (tf_iff_mulTorsionFree G).1 htf, hfp, α, β, hα, hβ, h⟩

/-! "Kaplansky's zero-divisor conjecture is false." -/

theorem A_false (H : MainTheorem) : type_of% @ReaderA.reading_kaplansky_false := by
  obtain ⟨G, _, -, htf, -, α, β, hα, hβ, h⟩ := H
  intro K
  rcases K (ZMod 2) G htf α β h with h' | h'
  · exact hα h'
  · exact hβ h'

theorem B_false (H : MainTheorem) : type_of% @ReaderB.reading_zerodiv_kaplansky_false := by
  obtain ⟨G, _, -, htf, -, α, β, hα, hβ, h⟩ := H
  intro K
  rcases K (ZMod 2) G ((tf_iff_B G).1 htf) α β h with h' | h'
  · exact hα h'
  · exact hβ h'

theorem C_false (H : MainTheorem) : type_of% @ReaderC.reading_kaplansky_is_false := by
  obtain ⟨G, _, -, htf, -, α, β, hα, hβ, h⟩ := H
  intro K
  exact K (ZMod 2) G ((tf_iff_mulTorsionFree G).1 htf) α β hα hβ h

/-! Reader B's classifying space, "Moreover" clause and full Theorem 1.1. -/

theorem cs_B (G : Type) [Group G] (h : HasFiniteTwoDimensionalClassifyingSpace G) :
    ReaderB.HasFiniteTwoDimClassifyingSpace G := by
  obtain ⟨X, topX, _, _, cw, hfin, hdim, -, x, ⟨e⟩, E, topE, hE, p, hp, -⟩ := h
  refine ⟨X, topX, inferInstance, cw, fun n hn => hdim n (by omega),
    fun n => hfin.finite_cell n, ⟨E, topE, p, hp.continuous, hp, hE⟩, x, ⟨?_⟩⟩
  exact (CategoryTheory.Aut.unitsEndEquivAut _).symm.trans (toUnits.symm.trans e.symm)

theorem B_moreover (H : MainTheorem) : type_of% @ReaderB.reading_zerodiv_moreover := by
  obtain ⟨G, _, hfp, htf, hcs, -⟩ := H
  exact ⟨G, _, fp_B G hfp, (tf_iff_B G).1 htf, cs_B G hcs⟩

theorem B_full (H : MainTheorem) : type_of% @ReaderB.reading_zerodiv_full := by
  obtain ⟨G, _, hfp, htf, hcs, α, β, hα, hβ, h⟩ := H
  exact ⟨G, _, fp_B G hfp, (tf_iff_B G).1 htf, ⟨α, β, hα, hβ, h⟩, cs_B G hcs⟩

end TargetO.ZeroDiv

#print axioms TargetO.ZeroDiv.A_thm
#print axioms TargetO.ZeroDiv.B_thm
#print axioms TargetO.ZeroDiv.C_thm
#print axioms TargetO.ZeroDiv.A_false
#print axioms TargetO.ZeroDiv.B_false
#print axioms TargetO.ZeroDiv.C_false
#print axioms TargetO.ZeroDiv.B_moreover
#print axioms TargetO.ZeroDiv.B_full
