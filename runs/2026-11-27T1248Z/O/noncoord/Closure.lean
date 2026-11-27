import Mathlib
import Readings.Noncoord
import ComparatorChallenges.CommutingDerivations

/-! # Target O, family O10: Theorem 1.1's noncoordinate claim closed against `CommutingDerivations`
(run 2026-11-27T1248Z, target O correction).

Run 2026-11-27T0628Z recorded "no frozen statement names F". Wrong: the family's scope document
`lean/docs/049.md` links a further challenge, `CommutingDerivations`, whose `OAI.AbhyankarSathaye.F` is the
manuscript's F term by term (h, u, v, w = X 0 .. X 3). Its theorem, at n = 4, says every element of the
common kernel of the derivations (which contains `extendedF`) is not the image of a variable under a
ℂ-algebra automorphism. `extendedF (le_refl 4)` is F (`fourInclusion` is the identity on `Fin 4`).
The frozen statement is taken with `type_of%`, never retyped. Still not stated in any Lean of the family:
R/(F) ≅ ℂ^[3] for this F (only `∃ F`, `AbhyankarSathaye`). -/

namespace TargetO.Noncoord2

open MvPolynomial

theorem extendedF_four : OAI.AbhyankarSathaye.extendedF (le_refl 4) = OAI.AbhyankarSathaye.F := by
  unfold OAI.AbhyankarSathaye.extendedF
  have : (OAI.AbhyankarSathaye.fourInclusion (le_refl 4)) = id := by
    funext i; rfl
  rw [this, rename_id]
  rfl

/-- The frozen theorem gives: the explicit F is not the image of any variable under any automorphism. -/
theorem frozen_F_noncoord
    (H : type_of% @OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras) :
    ¬ ∃ (e : MvPolynomial (Fin 4) ℂ ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ) (j : Fin 4),
      e (X j) = OAI.AbhyankarSathaye.F := by
  obtain ⟨d, -, -, -, -, hker, hnc, -⟩ := H 4 (le_refl 4)
  have hk : ∀ i, d i (OAI.AbhyankarSathaye.extendedF (le_refl 4)) = 0 :=
    (hker _).2 (Algebra.subset_adjoin rfl)
  have := hnc _ hk
  rwa [extendedF_four] at this

theorem F_A : ReaderA.ReadingO10A.F = OAI.AbhyankarSathaye.F := by
  simp only [ReaderA.ReadingO10A.F, ReaderA.ReadingO10A.p, ReaderA.ReadingO10A.x,
    ReaderA.ReadingO10A.y, ReaderA.ReadingO10A.s, ReaderA.ReadingO10A.h, ReaderA.ReadingO10A.u,
    ReaderA.ReadingO10A.v, ReaderA.ReadingO10A.w, OAI.AbhyankarSathaye.F, OAI.AbhyankarSathaye.p,
    OAI.AbhyankarSathaye.P, OAI.AbhyankarSathaye.x, OAI.AbhyankarSathaye.y, OAI.AbhyankarSathaye.s,
    OAI.AbhyankarSathaye.S, OAI.AbhyankarSathaye.h, OAI.AbhyankarSathaye.u, OAI.AbhyankarSathaye.v,
    OAI.AbhyankarSathaye.w] <;> ring

theorem F_B : ReaderB.ReadingB.F = OAI.AbhyankarSathaye.F := by
  simp only [ReaderB.ReadingB.F, ReaderB.ReadingB.p, ReaderB.ReadingB.x,
    ReaderB.ReadingB.y, ReaderB.ReadingB.s, ReaderB.ReadingB.h, ReaderB.ReadingB.u,
    ReaderB.ReadingB.v, ReaderB.ReadingB.w, OAI.AbhyankarSathaye.F, OAI.AbhyankarSathaye.p,
    OAI.AbhyankarSathaye.P, OAI.AbhyankarSathaye.x, OAI.AbhyankarSathaye.y, OAI.AbhyankarSathaye.s,
    OAI.AbhyankarSathaye.S, OAI.AbhyankarSathaye.h, OAI.AbhyankarSathaye.u, OAI.AbhyankarSathaye.v,
    OAI.AbhyankarSathaye.w] <;> ring

theorem F_C : ReaderC.O10Reading.FF = OAI.AbhyankarSathaye.F := by
  simp only [ReaderC.O10Reading.FF, ReaderC.O10Reading.pP, ReaderC.O10Reading.xX,
    ReaderC.O10Reading.yY, ReaderC.O10Reading.sS, OAI.AbhyankarSathaye.F, OAI.AbhyankarSathaye.p,
    OAI.AbhyankarSathaye.P, OAI.AbhyankarSathaye.x, OAI.AbhyankarSathaye.y, OAI.AbhyankarSathaye.s,
    OAI.AbhyankarSathaye.S, OAI.AbhyankarSathaye.h, OAI.AbhyankarSathaye.u, OAI.AbhyankarSathaye.v,
    OAI.AbhyankarSathaye.w] <;> ring

theorem A_noncoord
    (H : type_of% @OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras) :
    type_of% @ReaderA.ReadingO10A.reading_thm_noncoordinate := by
  rintro ⟨e, i, he⟩
  exact frozen_F_noncoord H ⟨e, i, he.trans F_A⟩

theorem B_noncoord
    (H : type_of% @OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras) :
    type_of% @ReaderB.ReadingB.reading_thm_noncoordinate := by
  rintro ⟨e, he⟩
  exact frozen_F_noncoord H ⟨e, _, he.trans F_B⟩

theorem C_noncoord
    (H : type_of% @OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras) :
    type_of% @ReaderC.O10Reading.reading_thm_noncoordinate := by
  rintro ⟨e, i, he⟩
  exact frozen_F_noncoord H ⟨e, i, he.trans F_C⟩

end TargetO.Noncoord2

#print axioms TargetO.Noncoord2.A_noncoord
#print axioms TargetO.Noncoord2.B_noncoord
#print axioms TargetO.Noncoord2.C_noncoord
