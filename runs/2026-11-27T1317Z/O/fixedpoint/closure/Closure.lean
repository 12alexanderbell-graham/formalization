import Mathlib
import Readings.FixedPoint
import ComparatorChallenges.ReflexiveFixedPoints

/-! # Target O, family O38 (reflexive fixed points): closures (run 2026-11-27T1317Z).
Frozen statement taken with `type_of%`, never retyped. Theorem 1.1: readers A, B, C. Reader C omits
`CompleteSpace`: a space whose canonical map into the bidual is onto is complete (the map is an isometry onto a
complete space), proved here. Corollary 1.2 (commuting families, via Bruck's theorem) has no Lean statement. -/

namespace TargetO.FixedPoint

universe u

theorem A_thm (H : type_of% @OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive.{u}) :
    type_of% @ReaderA.reading_thm_1_1.{u} := by
  intro X _ _ _ hX C hne hcl hb hconv F hF
  exact H hX C hne hcl hb hconv F hF

theorem B_thm (H : type_of% @OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive.{u}) :
    type_of% @ReaderB.readingMain.{u} := by
  intro X _ _ _ hX C hne hcl hb hconv F hF
  exact H hX C hne hcl hb hconv F hF

/-- Surjective canonical embedding into the bidual forces completeness. -/
theorem complete_of_reflexive {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hX : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)) : CompleteSpace X := by
  let e := NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := X)
  have hs : Function.Surjective e := hX
  let E := LinearIsometryEquiv.ofSurjective e hs
  exact (completeSpace_congr (e := E.toEquiv) E.isometry.isUniformEmbedding).2 inferInstance

theorem C_thm (H : type_of% @OAI.ReflexiveFixedPoints.exists_fixedPoint_of_canonicallyReflexive.{u}) :
    type_of% @ReaderC.reading_fixedpoint_thm1.{u} := by
  intro X _ _ hX C hne hcl hb hconv F hF
  have := complete_of_reflexive hX
  exact H hX C hne hcl hb hconv F hF

/-- Non-vacuity: the frozen statement's hypotheses are satisfiable (ℝ is reflexive, C = {0}). -/
theorem nonvacuous : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ ℝ) := by
  intro φ
  refine ⟨φ (ContinuousLinearMap.id ℝ ℝ), ?_⟩
  ext f
  rw [NormedSpace.dual_def]
  have hf : f = f 1 • ContinuousLinearMap.id ℝ ℝ := by ext; simp
  have h1 : f (φ (ContinuousLinearMap.id ℝ ℝ)) = φ (ContinuousLinearMap.id ℝ ℝ) * f 1 := by
    conv_lhs => rw [hf]
    simp [mul_comm]
  rw [h1]
  conv_rhs => rw [hf]
  rw [map_smul, smul_eq_mul, mul_comm]

end TargetO.FixedPoint

#print axioms TargetO.FixedPoint.A_thm
#print axioms TargetO.FixedPoint.B_thm
#print axioms TargetO.FixedPoint.C_thm
#print axioms TargetO.FixedPoint.nonvacuous
