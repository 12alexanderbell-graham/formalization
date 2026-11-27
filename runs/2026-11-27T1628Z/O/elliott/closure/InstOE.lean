import Mathlib
import Closure.Elliott

/-! # Target O, family O60: the Theorem 1.2 closures of `Closure.Elliott` instantiated with the frozen theorem of the
challenge `OrdinaryElliott` (run 2026-11-27T1628Z). -/

namespace TargetO.Elliott

theorem reading_A2_oe : type_of% @ReaderA.reading_thm_1_2 :=
  closure_A_oe OAI.OrdinaryCorrelations.binary_corrected_elliott
theorem reading_B2_oe : type_of% @ReaderB.readingThm1_2 :=
  closure_B_oe OAI.OrdinaryCorrelations.binary_corrected_elliott
theorem reading_C2_oe : type_of% @ReaderC.reading_binary_corrected_elliott :=
  closure_C_oe OAI.OrdinaryCorrelations.binary_corrected_elliott

end TargetO.Elliott

#print axioms TargetO.Elliott.reading_A2_oe
#print axioms TargetO.Elliott.reading_B2_oe
#print axioms TargetO.Elliott.reading_C2_oe
