import Mathlib
import Readings.QRH
import ComparatorChallenges.QuasiRiemannHypothesis
import ComparatorChallenges.DirichletSevenEighths

/-! # Target O, quasi-RH family: closures of the blind readings (run 2026-11-27T0628Z)

Frozen statements are taken with `type_of%` from the release's comparator challenges, never retyped.
Closed here: the ζ and Dirichlet readings (both manuscripts' constants). Not closed: every
`ReadingHecke` (Hecke L-functions over ℚ(√-3)); the frozen Hecke challenge uses the release's own
`LFunction` and `Character`, and relating them to a reader's ray-class characters is open. -/

namespace TargetO.QRH

theorem zeta_one_ne : riemannZeta 1 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)

/-- Frozen ζ statement ⟺ each reader's ζ reading at 7/8 (the frozen statement also covers s = 1, where
Mathlib's value is nonzero). -/
theorem zeta_A : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) ↔
    ReaderA.QRHReadingA.ReadingZeta (7 / 8) :=
  ⟨fun h s hs _ => h hs, fun h s hs => by
    by_cases h1 : s = 1
    · subst h1; exact zeta_one_ne
    · exact h s hs h1⟩

theorem zeta_B : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) ↔
    ReaderB.ReadingZeta (7 / 8) :=
  ⟨fun h s hs _ => h hs, fun h s hs => by
    by_cases h1 : s = 1
    · subst h1; exact zeta_one_ne
    · exact h s hs h1⟩

theorem zeta_C : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) ↔
    ReaderC.QRHReadingC.ReadingZeta (7 / 8) :=
  ⟨fun h s hs _ => h hs, fun h s hs => by
    by_cases h1 : s = 1
    · subst h1; exact zeta_one_ne
    · exact h s hs h1⟩

/-- Frozen Dirichlet statement ⟺ each reader's all-character reading at 7/8. -/
theorem dir_A : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) ↔
    ReaderA.QRHReadingA.ReadingDirichlet (7 / 8) :=
  ⟨fun h N _ χ s hs hp => h χ hs (fun ⟨a, b⟩ => hp a b),
   fun h q _ χ s hs hp => h q χ s hs (fun a b => hp ⟨a, b⟩)⟩

theorem dir_B : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) ↔
    ReaderB.ReadingDirichlet (7 / 8) :=
  ⟨fun h N _ χ s hs hp => h χ hs (fun ⟨a, b⟩ => hp.elim (· a) (· b)),
   fun h q _ χ s hs hp => h q χ s hs (by tauto)⟩

theorem dir_C : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) ↔
    ReaderC.QRHReadingC.ReadingDirichlet (7 / 8) :=
  ⟨fun h N _ χ s hs hp => h χ hs (fun ⟨a, b⟩ => hp b a),
   fun h q _ χ s hs hp => h q χ s hs (fun b a => hp ⟨a, b⟩)⟩

/-! The 5 October constants (11/12 > 7/8) follow from the frozen 7/8 statements. -/

theorem zeta_A_1112 : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) →
    ReaderA.QRHReadingA.ReadingZeta (11 / 12) :=
  fun h s hs _ => h (by linarith)

theorem zeta_B_1112 : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) →
    ReaderB.ReadingZeta (11 / 12) :=
  fun h s hs _ => h (by linarith)

theorem zeta_C_1112 : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) →
    ReaderC.QRHReadingC.ReadingZeta (11 / 12) :=
  fun h s hs _ => h (by linarith)

theorem dirPrim_A_1112 : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderA.QRHReadingA.ReadingDirichletPrim (11 / 12) :=
  fun h N _ χ _ s hs hp => h χ (by linarith) (fun ⟨a, b⟩ => hp a b)

theorem dirPrim_B_1112 : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderB.ReadingDirichletPrim (11 / 12) :=
  fun h N _ χ _ s hs hp => h χ (by linarith) (fun ⟨a, b⟩ => hp.elim (· a) (· b))

theorem dirPrim_C_1112 : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderC.QRHReadingC.ReadingDirichletPrim (11 / 12) :=
  fun h N _ χ s _ hs hp => h χ (by linarith) (fun ⟨a, b⟩ => hp b a)

/-- Also at 7/8 for the primitive readings (the frozen statement covers every character). -/
theorem dirPrim_A : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderA.QRHReadingA.ReadingDirichletPrim (7 / 8) :=
  fun h N _ χ _ s hs hp => h χ hs (fun ⟨a, b⟩ => hp a b)

end TargetO.QRH

#print axioms TargetO.QRH.zeta_A
#print axioms TargetO.QRH.zeta_B
#print axioms TargetO.QRH.zeta_C
#print axioms TargetO.QRH.dir_A
#print axioms TargetO.QRH.dir_B
#print axioms TargetO.QRH.dir_C
#print axioms TargetO.QRH.zeta_A_1112
#print axioms TargetO.QRH.zeta_B_1112
#print axioms TargetO.QRH.zeta_C_1112
#print axioms TargetO.QRH.dirPrim_A_1112
#print axioms TargetO.QRH.dirPrim_B_1112
#print axioms TargetO.QRH.dirPrim_C_1112
#print axioms TargetO.QRH.dirPrim_A
