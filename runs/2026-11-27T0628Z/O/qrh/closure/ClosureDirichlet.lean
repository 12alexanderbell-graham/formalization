import Mathlib
import Readings.QRH
import ComparatorChallenges.DirichletSevenEighths

/-! # Target O, quasi-RH family: closures of the Dirichlet readings (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped. Generated from Closure.lean (split per replay line). -/

namespace TargetO.QRH

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

theorem dirPrim_A_1112 : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderA.QRHReadingA.ReadingDirichletPrim (11 / 12) :=
  fun h N _ χ _ s hs hp => h χ (by linarith) (fun ⟨a, b⟩ => hp a b)

theorem dirPrim_B_1112 : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderB.ReadingDirichletPrim (11 / 12) :=
  fun h N _ χ _ s hs hp => h χ (by linarith) (fun ⟨a, b⟩ => hp.elim (· a) (· b))

theorem dirPrim_C_1112 : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderC.QRHReadingC.ReadingDirichletPrim (11 / 12) :=
  fun h N _ χ s _ hs hp => h χ (by linarith) (fun ⟨a, b⟩ => hp b a)

theorem dirPrim_A : (type_of% @OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re) →
    ReaderA.QRHReadingA.ReadingDirichletPrim (7 / 8) :=
  fun h N _ χ _ s hs hp => h χ hs (fun ⟨a, b⟩ => hp a b)

end TargetO.QRH

#print axioms TargetO.QRH.dir_A
#print axioms TargetO.QRH.dir_B
#print axioms TargetO.QRH.dir_C
#print axioms TargetO.QRH.dirPrim_A_1112
#print axioms TargetO.QRH.dirPrim_B_1112
#print axioms TargetO.QRH.dirPrim_C_1112
#print axioms TargetO.QRH.dirPrim_A
