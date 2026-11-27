import Mathlib
import Readings.SepQuot
import ComparatorChallenges.SeparableQuotientNegative

/-! # Target O, family O31 (relative independence of the separable quotient problem): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped: `negative_main` — CH (#ℝ = ℵ₁) implies
¬SQ_ℝ ∧ ¬SQ_ℂ at every universe of Banach spaces. Closed: reader A's (ii) (A's SQ over ℝ or ℂ is the frozen one;
A's CH is 𝔠 = ℵ₁ with #ℝ = 𝔠). Not closed: every reader's (i) (real-valued measurable 𝔠 ⇒ SQ: no Lean
statement), the consistency conclusions (not statable, as all three readers note), and (ii) for readers B and C:
B states it for every `RCLike 𝕜` and C for a type 𝕜 equal to ℝ or ℂ but with an arbitrary `RCLike` instance — the
frozen statement is about ℝ and ℂ with their own structures, and transporting along an `RCLike` isomorphism is not
written here. -/

namespace TargetO.SepQuot

universe u

theorem sq_A {𝕜 : Type} [RCLike 𝕜] (h : ReaderA.SQ.{u} 𝕜) : OAI.SeparableQuotient.SQ.{u} 𝕜 := by
  intro X _ _ _ hX
  obtain ⟨Y, i1, i2, i3, hs, hf, T, hT⟩ := h X hX
  exact ⟨Y, i1, i2, i3, hs, hf, T, hT⟩

theorem A_ii : (type_of% @OAI.SeparableQuotient.negative_main.{u}) → (type_of% @ReaderA.reading_ii.{u}) := by
  intro h hCH
  have hCH' : OAI.SeparableQuotient.CH := by
    unfold OAI.SeparableQuotient.CH
    rw [Cardinal.mk_real]; exact hCH
  obtain ⟨h1, h2⟩ := h hCH'
  exact ⟨fun hA => h1 (sq_A hA), fun hA => h2 (sq_A hA)⟩

end TargetO.SepQuot

#print axioms TargetO.SepQuot.A_ii
