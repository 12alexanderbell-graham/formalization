import Mathlib
import Readings.kadison
import ComparatorChallenges.KadisonSimilarity

/-! # Target O, family O62 (Kadison's similarity problem), Theorem 1.1: closures (run 2026-11-27T1628Z).

Frozen statement `OAI.KadisonSimilarity.similarityTheorem : SimilarityTheorem` (taken by name, never retyped): for
every unital C⋆-algebra `A` and Hilbert space `K` (any universes `u`, `v`), every continuous unital algebra
homomorphism `π : A →ₐ[ℂ] B(K)` has an invertible `S` with `S π(a⋆) S⁻¹ = (S π(a) S⁻¹)⋆`.

Links: each reader's boundedness `‖π a‖ ≤ c ‖a‖` gives the frozen continuity
(`AddMonoidHomClass.continuous_of_bound`); the frozen identity is reader B's (sides swapped) and reader A's star
form; reader A's `ρ : A →⋆ₐ[ℂ] B(H)` with `ρ a = S π(a) S⁻¹` and reader C's (with `S T = T S = 1`) are built from
the frozen unit (`conjHom`: conjugation by a unit composed with `π` is an algebra homomorphism, and the frozen identity
makes it preserve `⋆`). Theorems 1.2 and Corollary 1.3 are not closed in this module (see `EXTERNAL_O.md`, O62). -/

namespace TargetO.Kadison

open OAI.KadisonSimilarity

universe u v

variable {A : Type u} [CStarAlgebra A] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem cont_of_bound (π : A →ₐ[ℂ] (H →L[ℂ] H)) (h : ∃ c : ℝ, ∀ a : A, ‖π a‖ ≤ c * ‖a‖) : Continuous π := by
  obtain ⟨c, hc⟩ := h
  exact AddMonoidHomClass.continuous_of_bound π c hc

/-- Conjugation by a unit, composed with `π`, as an algebra homomorphism. -/
noncomputable def conjHom (π : A →ₐ[ℂ] (H →L[ℂ] H)) (S : (H →L[ℂ] H)ˣ) : A →ₐ[ℂ] (H →L[ℂ] H) where
  toFun a := (S : H →L[ℂ] H) * π a * ↑S⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    calc (S : H →L[ℂ] H) * (π a * π b) * ↑S⁻¹
        = (S : H →L[ℂ] H) * π a * (↑S⁻¹ * (S : H →L[ℂ] H)) * π b * ↑S⁻¹ := by
          rw [Units.inv_mul, mul_one]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' a b := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one]
    rw [mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv]

/-- With the frozen identity, the conjugate is a `⋆`-homomorphism. -/
noncomputable def conjStarHom (π : A →ₐ[ℂ] (H →L[ℂ] H)) (S : (H →L[ℂ] H)ˣ)
    (hS : ∀ a : A, (S : H →L[ℂ] H) * π (star a) * ↑S⁻¹ = star ((S : H →L[ℂ] H) * π a * ↑S⁻¹)) :
    A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  { conjHom π S with map_star' := fun a => hS a }

theorem frozen_at (frozen : type_of% @similarityTheorem.{u, v}) (π : A →ₐ[ℂ] (H →L[ℂ] H))
    (h : ∃ c : ℝ, ∀ a : A, ‖π a‖ ≤ c * ‖a‖) :
    ∃ S : (H →L[ℂ] H)ˣ, ∀ a : A,
      (S : H →L[ℂ] H) * π (star a) * ↑S⁻¹ = star ((S : H →L[ℂ] H) * π a * ↑S⁻¹) :=
  frozen A H ⟨π, cont_of_bound π h⟩

theorem closure_A_star (frozen : type_of% @similarityTheorem.{u, v}) :
    type_of% @ReaderA.reading_thm_1_1_similarity_star.{u, v} := by
  intro A _ H _ _ _ π hπ
  exact frozen_at frozen π hπ

theorem closure_A (frozen : type_of% @similarityTheorem.{u, v}) :
    type_of% @ReaderA.reading_thm_1_1_similarity.{u, v} := by
  intro A _ H _ _ _ π hπ
  obtain ⟨S, hS⟩ := frozen_at frozen π hπ
  exact ⟨S, conjStarHom π S hS, fun a => rfl⟩

theorem closure_B (frozen : type_of% @similarityTheorem.{u, v}) :
    type_of% @ReaderB.readingSimilarity.{u, v} := by
  intro A _ H _ _ _ π hπ
  obtain ⟨S, hS⟩ := frozen_at frozen π hπ
  exact ⟨S, fun a => (hS a).symm⟩

theorem closure_C (frozen : type_of% @similarityTheorem.{u, u}) :
    type_of% @ReaderC.reading_thm_1_1.{u} := by
  intro A _ H _ _ _ π hπ
  obtain ⟨S, hS⟩ := frozen_at frozen π hπ
  exact ⟨S, ↑S⁻¹, Units.mul_inv S, Units.inv_mul S, conjStarHom π S hS, fun a => rfl,
    fun a => map_star _ a⟩

theorem reading_A_closed : type_of% @ReaderA.reading_thm_1_1_similarity.{u, v} := closure_A similarityTheorem
theorem reading_A_star_closed : type_of% @ReaderA.reading_thm_1_1_similarity_star.{u, v} :=
  closure_A_star similarityTheorem
theorem reading_B_closed : type_of% @ReaderB.readingSimilarity.{u, v} := closure_B similarityTheorem
theorem reading_C_closed : type_of% @ReaderC.reading_thm_1_1.{u} := closure_C similarityTheorem

end TargetO.Kadison

#print axioms TargetO.Kadison.closure_A
#print axioms TargetO.Kadison.closure_A_star
#print axioms TargetO.Kadison.closure_B
#print axioms TargetO.Kadison.closure_C
