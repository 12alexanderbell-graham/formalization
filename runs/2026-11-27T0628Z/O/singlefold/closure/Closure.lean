import Mathlib
import Readings.SingleFold
import ComparatorChallenges.SingleFold

/-! # Target O, family O24 (single-fold Diophantine representations): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: for n ≥ 1 and S ⊆ ℕⁿ with `REPred`, some m ≥ 1 and
P ∈ ℤ[A, W] with `a ∈ S ↔ ∃ w, P(a, w) = 0` and any two zeros w, v at the same a equal. Closed (frozen ⇒
reading): every reader's Theorem 1.1 — exactly one witness on S (A and C: `encard = 1`; B: `∃!`), none off S
(A and C: `encard = 0`; B: no zero). The evaluation maps are the frozen one under each reader's name. Not
closed: every reader's Corollary (undecidability under the at-most-one-solution promise): no Lean statement. -/

namespace TargetO.SingleFold

theorem count {n m : ℕ} {S : Set (Fin n → ℕ)} {P : MvPolynomial (Fin n ⊕ Fin m) ℤ}
    (hP : OAI.SingleFold.Represents P S) (a : Fin n → ℕ) :
    (a ∈ S → Set.encard {w : Fin m → ℕ | OAI.SingleFold.evalNat P a w = 0} = 1) ∧
    (a ∉ S → Set.encard {w : Fin m → ℕ | OAI.SingleFold.evalNat P a w = 0} = 0) := by
  obtain ⟨hiff, huniq⟩ := hP a
  constructor
  · intro ha
    obtain ⟨w, hw⟩ := hiff.mp ha
    rw [Set.encard_eq_one]
    refine ⟨w, Set.eq_singleton_iff_unique_mem.mpr ⟨hw, fun v hv => huniq v w hv hw⟩⟩
  · intro ha
    rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
    intro w hw
    exact ha (hiff.mpr ⟨w, hw⟩)

theorem A_thm : (type_of% @OAI.SingleFold.main) → (type_of% @ReaderA.reading_thm_1_1) := by
  intro h n hn S hS
  obtain ⟨m, hm, P, hP⟩ := h n hn S hS
  exact ⟨m, hm, P, fun a => count hP a⟩

theorem C_thm : (type_of% @OAI.SingleFold.main) → (type_of% @ReaderC.reading_singlefold_main) := by
  intro h n hn S hS
  obtain ⟨m, hm, P, hP⟩ := h n hn S hS
  exact ⟨m, hm, P, fun a => count hP a⟩

theorem B_thm : (type_of% @OAI.SingleFold.main) → (type_of% @ReaderB.reading_singlefold_main) := by
  intro h n hn S hS
  obtain ⟨m, hm, P, hP⟩ := h n hn S hS
  refine ⟨m, hm, P, fun a => ⟨fun ha => ?_, fun ha w hw => ha ((hP a).1.mpr ⟨w, hw⟩)⟩⟩
  obtain ⟨w, hw⟩ := (hP a).1.mp ha
  exact ⟨w, hw, fun v hv => (hP a).2 v w hv hw⟩

end TargetO.SingleFold

#print axioms TargetO.SingleFold.A_thm
#print axioms TargetO.SingleFold.B_thm
#print axioms TargetO.SingleFold.C_thm
