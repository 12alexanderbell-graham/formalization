import Mathlib
import Readings.Matroid
import ComparatorChallenges.InfiniteMatroid

/-! # Target O, family O37 (the infinite matroid packing/covering conjecture): closures, first challenge
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped: `main` — the countably infinite type
E = ℤ × (Σ m, (Fin m → Bool) → Bool), two self-dual matroids on it with no independent covering and no
packing/covering partition (`HasPackingCovering`: restriction-spanning sets in P, independent sets of the
contraction onto C written (M✶ ↾ C)✶). A reader's partition gives the frozen one: closure of S in M ↾ P equal to P
with S ⊆ P is `Spanning`; reader B's contraction M ／ (E \ C) is (M✶ ↾ C)✶ when C ⊆ E (definitional, via
`delete_eq_restrict`). Closed: reader A's Theorem 1.1 and its "the conjecture is false", reader B's Theorem 1.1,
reader C's three Theorem 1.1 readings. Corollary 1.4 readings (A: three, B: one, C: two) are against the second
challenge (`InfiniteMatroidCorollaries`), whose names clash with this one; not written this run. -/

open Matroid Set

namespace TargetO.Matroid

open OAI.InfiniteMatroidCounterexample

theorem pc_of {α : Type*} {M₀ M₁ : Matroid α} (h0 : M₀.E = univ) (h1 : M₁.E = univ)
    {P C S₀ S₁ I₀ I₁ : Set α} (hPC : Disjoint P C) (hU : P ∪ C = univ) (hS₀ : S₀ ⊆ P) (hS₁ : S₁ ⊆ P)
    (hd : Disjoint S₀ S₁) (hc₀ : (M₀.restrict P).closure S₀ = P) (hc₁ : (M₁.restrict P).closure S₁ = P)
    (hI₀ : I₀ ⊆ C) (hI₁ : I₁ ⊆ C) (hi₀ : (M₀.dual.restrict C).dual.Indep I₀)
    (hi₁ : (M₁.dual.restrict C).dual.Indep I₁) (hIU : I₀ ∪ I₁ = C) : HasPackingCovering M₀ M₁ := by
  refine ⟨P, C, S₀, S₁, I₀, I₁, hPC, by rw [hU, h0], by rw [h1, h0], hS₀, hS₁, hd, ?_, ?_, hI₀, hI₁,
    hi₀, hi₁, hIU⟩
  · exact ⟨by rw [hc₀]; rfl, hS₀⟩
  · exact ⟨by rw [hc₁]; rfl, hS₁⟩

theorem contract_eq {α : Type*} (M : Matroid α) {C : Set α} (hC : C ⊆ M.E) :
    M.contract (M.E \ C) = (M.dual.restrict C).dual := by
  rw [← dual_delete_dual, delete_eq_restrict, dual_ground, diff_diff_cancel_left hC]

theorem A_main : (type_of% @OAI.InfiniteMatroidCounterexample.main) → (type_of% @ReaderA.reading_main) := by
  rintro ⟨hc, hi, M₀, M₁, h0, h1, d0, d1, hcov, hpc⟩
  refine ⟨E, univ, M₀, M₁, countable_univ, infinite_univ, h0, h1, d0, d1, hcov, ?_⟩
  rintro ⟨P, C, S, I, hPC, hU, hS, hI, hd, hcl, hin, hIU⟩
  apply hpc
  refine pc_of h0 h1 hPC hU (hS 0) (hS 1) (hd 0 1 (by decide)) (hcl 0) (hcl 1) (hI 0) (hI 1) (hin 0) (hin 1) ?_
  rw [← hIU]; ext x; simp [Fin.exists_fin_two]

theorem A_false : (type_of% @OAI.InfiniteMatroidCounterexample.main) →
    (type_of% @ReaderA.reading_conjecture_false) := by
  intro h hall
  obtain ⟨α, F, M0, M1, -, -, h0, h1, -, -, -, hpc⟩ := A_main h
  exact hpc (hall α F (Fin 2) _ (fun i => by
    by_cases hi : i = 0
    · simp only [hi, if_true]; exact h0
    · simp only [hi, if_false]; exact h1))

theorem B_main : (type_of% @OAI.InfiniteMatroidCounterexample.main) →
    (type_of% @ReaderB.readingMatroidMain) := by
  rintro ⟨hc, hi, M₀, M₁, h0, h1, d0, d1, hcov, hpc⟩
  refine ⟨E, hc, hi, M₀, M₁, h0, h1, d0, d1, hcov, ?_⟩
  rintro ⟨P, C, S, I, hPC, hU, hS, hI, hd, hcl, hin, hIU⟩
  apply hpc
  have hin' : ∀ b : Bool, ((if b then M₁ else M₀).dual.restrict C).dual.Indep (I b) := by
    intro b
    have := hin b
    unfold ReaderB.contractOnto at this
    rwa [contract_eq _ (by cases b <;> simp [h0, h1])] at this
  refine pc_of h0 h1 hPC hU (hS false) (hS true) (hd false true (by decide)) (hcl false) (hcl true)
    (hI false) (hI true) (hin' false) (hin' true) ?_
  rw [← hIU]; ext x; simp [or_comm]

theorem C_main : (type_of% @OAI.InfiniteMatroidCounterexample.main) → (type_of% @ReaderC.reading_main) := by
  rintro ⟨hc, hi, M₀, M₁, h0, h1, d0, d1, hcov, hpc⟩
  refine ⟨E, ![M₀, M₁], ⟨hc, hi, fun i => by fin_cases i <;> simp [h0, h1],
    fun i => by fin_cases i <;> simp [d0, d1]⟩, hcov, ?_⟩
  rintro ⟨P, C, S, I, hU, hPC, hS, hd, hcl, hI, hin, hIU⟩
  apply hpc
  refine pc_of h0 h1 hPC hU (hS 0) (hS 1) (hd 0 1 (by decide)) (hcl 0) (hcl 1) (hI 0) (hI 1) (hin 0) (hin 1) ?_
  rw [← hIU]; ext x; simp [Fin.exists_fin_two]

theorem C_cover : (type_of% @OAI.InfiniteMatroidCounterexample.main) →
    (type_of% @ReaderC.reading_no_independent_covering) := by
  intro h
  obtain ⟨α, M, hp, hcov, -⟩ := C_main h
  exact ⟨α, M, hp, hcov⟩

theorem C_pc : (type_of% @OAI.InfiniteMatroidCounterexample.main) →
    (type_of% @ReaderC.reading_no_packing_covering_partition) := by
  intro h
  obtain ⟨α, M, hp, -, hpc⟩ := C_main h
  exact ⟨α, M, hp, hpc⟩

end TargetO.Matroid

#print axioms TargetO.Matroid.A_main
#print axioms TargetO.Matroid.A_false
#print axioms TargetO.Matroid.B_main
#print axioms TargetO.Matroid.C_main
#print axioms TargetO.Matroid.C_cover
#print axioms TargetO.Matroid.C_pc
