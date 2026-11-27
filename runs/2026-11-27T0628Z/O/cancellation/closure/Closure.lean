import Mathlib
import Readings.Cancellation
import ComparatorChallenges.ComplexCancellation

/-! # Target O, family O33 (an explicit failure of complex affine space cancellation): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped: `MainStatement` — for
A = ℂ[p,s,u,F,J]/(H) (variables `X 0 … X 4` in that order, H as in the source), A is of finite type, a domain, of
Krull dimension 4, A[w] ≃ₐ[ℂ] ℂ[5 variables] and A ≄ₐ[ℂ] ℂ[4 variables]. Every reader wrote the same variables in
the same order, so each reader's A is the frozen A by unfolding (`rfl`). Closed: every reader's Theorem 1.1 (A's four
parts and their conjunction). Not closed: every reader's Corollary 1.2 (H is not a coordinate of P but is one of
P[w]; the Stable Coordinate Conjecture fails): the release has no Lean statement of it. -/

namespace TargetO.Cancellation

theorem A_eq : ReaderA.H = OAI.ComplexCancellation.H := rfl
theorem B_eq : ReaderB.H = OAI.ComplexCancellation.H := rfl
theorem C_eq : ReaderC.Hpoly (k := ℂ) = OAI.ComplexCancellation.H := rfl

theorem A_thm : (type_of% @OAI.ComplexCancellation.main) → (type_of% @ReaderA.reading_thm_1_1) := by
  rintro ⟨-, h1, h2, h3, h4⟩
  unfold ReaderA.A
  rw [A_eq]
  exact ⟨h1, h2, h3, h4⟩

theorem A_integral : (type_of% @OAI.ComplexCancellation.main) → (type_of% @ReaderA.reading_thm_1_1_integral) :=
  fun h => (A_thm h).1
theorem A_dim : (type_of% @OAI.ComplexCancellation.main) → (type_of% @ReaderA.reading_thm_1_1_dim) :=
  fun h => (A_thm h).2.1
theorem A_cylinder : (type_of% @OAI.ComplexCancellation.main) →
    (type_of% @ReaderA.reading_thm_1_1_cylinder) := fun h => (A_thm h).2.2.1
theorem A_not_affine : (type_of% @OAI.ComplexCancellation.main) →
    (type_of% @ReaderA.reading_thm_1_1_not_affine) := fun h => (A_thm h).2.2.2

theorem B_thm : (type_of% @OAI.ComplexCancellation.main) →
    (type_of% @ReaderB.reading_cancellation_main) := by
  rintro ⟨-, h1, h2, h3, h4⟩
  unfold ReaderB.A
  rw [B_eq]
  exact ⟨h1, h2, h3, h4⟩

theorem C_thm : (type_of% @OAI.ComplexCancellation.main) →
    (type_of% @ReaderC.reading_cancellation_thm11) := by
  rintro ⟨-, h1, h2, h3, h4⟩
  unfold ReaderC.Aalg
  rw [C_eq]
  exact ⟨h1, h2, h3, not_nonempty_iff.mp h4⟩

end TargetO.Cancellation

#print axioms TargetO.Cancellation.A_thm
#print axioms TargetO.Cancellation.A_integral
#print axioms TargetO.Cancellation.A_dim
#print axioms TargetO.Cancellation.A_cylinder
#print axioms TargetO.Cancellation.A_not_affine
#print axioms TargetO.Cancellation.B_thm
#print axioms TargetO.Cancellation.C_thm
