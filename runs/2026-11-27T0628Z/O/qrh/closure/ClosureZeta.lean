import Mathlib
import Readings.QRH
import ComparatorChallenges.QuasiRiemannHypothesis

/-! # Target O, quasi-RH family: closures of the ζ readings (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped. Generated from Closure.lean (split per replay line). -/

namespace TargetO.QRH

theorem zeta_one_ne : riemannZeta 1 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)

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

theorem zeta_A_1112 : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) →
    ReaderA.QRHReadingA.ReadingZeta (11 / 12) :=
  fun h s hs _ => h (by linarith)

theorem zeta_B_1112 : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) →
    ReaderB.ReadingZeta (11 / 12) :=
  fun h s hs _ => h (by linarith)

theorem zeta_C_1112 : (type_of% @OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re) →
    ReaderC.QRHReadingC.ReadingZeta (11 / 12) :=
  fun h s hs _ => h (by linarith)

end TargetO.QRH

#print axioms TargetO.QRH.zeta_one_ne
#print axioms TargetO.QRH.zeta_A
#print axioms TargetO.QRH.zeta_B
#print axioms TargetO.QRH.zeta_C
#print axioms TargetO.QRH.zeta_A_1112
#print axioms TargetO.QRH.zeta_B_1112
#print axioms TargetO.QRH.zeta_C_1112
