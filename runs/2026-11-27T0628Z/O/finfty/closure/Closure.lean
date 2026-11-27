import Mathlib
import Readings.FInfty
import ComparatorChallenges.UniversalFInfinity

/-! # Target O, family O19 (a universal group of type F∞): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped (at universe 0, the readers' `Type`): a group `H` with
`HasTypeFInfinity H` (a Hausdorff connected space with a CW structure on `univ`, finitely many cells in each
dimension, π₁ ≃* H, and a surjective covering map from a contractible space) into which every
`Group.IsFinitelyPresented` group embeds. Closed: every reader's Theorem 1.1 (frozen ⇒ reading; readers B and
C ask less of the cover, reader A also asks continuity, which a covering map has; readers A and C's own
"finitely presented" — G ≃* ⟨n generators | a finite set of relators⟩ — gives Mathlib's). Not closed: every
reader's Corollary 1.2 (f.g. G embeds in H ⇔ G recursively presented): the release has no Lean statement of it,
and it rests on Higman's embedding theorem, which is not in Lean. -/

namespace TargetO.FInfty

/-- A reader's "finitely presented" gives Mathlib's. -/
theorem fp_of {G : Type} [Group G] {n : ℕ} {R : Finset (FreeGroup (Fin n))}
    (e : G ≃* PresentedGroup (R : Set (FreeGroup (Fin n)))) : Group.IsFinitelyPresented G :=
  Group.IsFinitelyPresented.equiv e.symm

theorem A_thm : (type_of% @OAI.UniversalFInfinity.universal_group_of_type_FInfinity.{0}) →
    (type_of% @ReaderA.reading_thm_1_1) := by
  intro h
  obtain ⟨H, gH, ⟨X, tX, t2, conn, cw, hfin, hπ, E, tE, cE, p, hsurj, hcov⟩, hemb⟩ := h
  refine ⟨H, gH, ⟨X, tX, t2, cw, hfin, conn, hπ, E, tE, p, hcov.continuous, hcov, hsurj, cE⟩, ?_⟩
  intro G _ ⟨n, R, ⟨e⟩⟩
  have := fp_of e
  exact hemb G

theorem B_thm : (type_of% @OAI.UniversalFInfinity.universal_group_of_type_FInfinity.{0}) →
    (type_of% @ReaderB.reading_thm_1_1) := by
  intro h
  obtain ⟨H, gH, ⟨X, tX, t2, conn, cw, hfin, hπ, E, tE, cE, p, hsurj, hcov⟩, hemb⟩ := h
  refine ⟨H, gH, ⟨X, tX, cw, conn, hfin, hπ, E, tE, p, hcov, cE⟩, ?_⟩
  intro G _ hG
  exact hemb G

theorem C_thm : (type_of% @OAI.UniversalFInfinity.universal_group_of_type_FInfinity.{0}) →
    (type_of% @ReaderC.FInfty.reading_finfty_universal) := by
  intro h
  obtain ⟨H, gH, ⟨X, tX, t2, conn, cw, hfin, hπ, E, tE, cE, p, hsurj, hcov⟩, hemb⟩ := h
  refine ⟨H, gH, ⟨X, tX, conn, ⟨cw, hfin⟩, hπ, E, tE, p, hcov, cE⟩, ?_⟩
  intro G _ ⟨n, R, ⟨e⟩⟩
  have := fp_of e
  exact hemb G

end TargetO.FInfty

#print axioms TargetO.FInfty.A_thm
#print axioms TargetO.FInfty.B_thm
#print axioms TargetO.FInfty.C_thm
