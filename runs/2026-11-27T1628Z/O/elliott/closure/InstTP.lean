import Mathlib
import Closure.Elliott

/-! # Target O, family O60: the closures of `Closure.Elliott` instantiated with the frozen theorems of the challenge
`OrdinaryTwoPointCorrelations` (run 2026-11-27T1628Z). A separate module, so that the replay of the family's other
challenge never sees this challenge's `sorry`. -/

namespace TargetO.Elliott

open OAI.OrdinaryTwoPointCorrelations

theorem reading_A1 : type_of% @ReaderA.reading_thm_1_1 := closure_A_thm1 liouville_log_saving
theorem reading_A2 : type_of% @ReaderA.reading_thm_1_2 := closure_A_thm2 binary_corrected_elliott
theorem reading_A3 : type_of% @ReaderA.reading_cor_1_3 := closure_A_cor affine_corrected_elliott
theorem reading_B1 : type_of% @ReaderB.readingThm1_1 := closure_B_thm1 liouville_log_saving
theorem reading_B2 : type_of% @ReaderB.readingThm1_2 := closure_B_thm2 binary_corrected_elliott
theorem reading_B3 : type_of% @ReaderB.readingCor1_3 := closure_B_cor affine_corrected_elliott
theorem reading_C1 : type_of% @ReaderC.reading_liouville_affine_saving := closure_C_thm1 liouville_log_saving
theorem reading_C2 : type_of% @ReaderC.reading_binary_corrected_elliott := closure_C_thm2 binary_corrected_elliott
theorem reading_C3 : type_of% @ReaderC.reading_affine_correlations := closure_C_cor affine_corrected_elliott

end TargetO.Elliott

#print axioms TargetO.Elliott.reading_A1
#print axioms TargetO.Elliott.reading_A2
#print axioms TargetO.Elliott.reading_A3
#print axioms TargetO.Elliott.reading_B1
#print axioms TargetO.Elliott.reading_B2
#print axioms TargetO.Elliott.reading_B3
#print axioms TargetO.Elliott.reading_C1
#print axioms TargetO.Elliott.reading_C2
#print axioms TargetO.Elliott.reading_C3
