import Mathlib
import Readings.Ramsey5
import ComparatorChallenges.RamseyFive

/-! # Target O, family O29 (the sharp logarithmic exponent of r(5,t)): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: `SharpBounds ∧ SharpExponent` with `ramsey s t` the least
n such that every `SimpleGraph (Fin n)` has an s-clique or a t-independent set (`IsNClique`, `IsNIndepSet`).
Each reader's r(s,t) is proved equal to the frozen `ramsey` (A and C: cliques/independent sets of given card; B:
`¬ CliqueFree` of G and of its complement), so the bounds (∀ᶠ = ∃ t₀) and the limit transfer. Frozen ⇒ reading. -/

open Filter Topology

namespace TargetO.Ramsey5

open OAI.SharpRamseyFive

theorem prop_A (s t n : ℕ) : ReaderA.RamseyProperty s t n ↔ RamseyProperty s t n := by
  refine forall_congr' fun G => ?_
  refine or_congr ⟨fun ⟨S, hc, hS⟩ => ⟨S, ⟨hS, hc⟩⟩, fun ⟨S, hS⟩ => ⟨S, hS.2, hS.1⟩⟩
    ⟨fun ⟨S, hc, hS⟩ => ⟨S, ⟨hS, hc⟩⟩, fun ⟨S, hS⟩ => ⟨S, hS.2, hS.1⟩⟩

theorem prop_C (s t n : ℕ) : ReaderC.IsRamseyGood s t n ↔ RamseyProperty s t n := by
  refine forall_congr' fun G => ?_
  refine or_congr ⟨fun ⟨S, hc, hS⟩ => ⟨S, ⟨hS, hc⟩⟩, fun ⟨S, hS⟩ => ⟨S, hS.2, hS.1⟩⟩
    ⟨fun ⟨S, hc, hS⟩ => ⟨S, ⟨hS, hc⟩⟩, fun ⟨S, hS⟩ => ⟨S, hS.2, hS.1⟩⟩

theorem prop_B (s t n : ℕ) :
    (∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t) ↔ RamseyProperty s t n := by
  refine forall_congr' fun G => ?_
  simp only [SimpleGraph.CliqueFree, not_forall, not_not]
  exact or_congr Iff.rfl ⟨fun ⟨S, hS⟩ => ⟨S, by simpa using hS⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa using hS⟩⟩

theorem rA : ReaderA.r = ramsey := by
  funext s t; unfold ReaderA.r ramsey; congr 1; ext n; exact prop_A s t n
theorem rB : ReaderB.r = ramsey := by
  funext s t; unfold ReaderB.r ramsey; congr 1; ext n; exact prop_B s t n
theorem rC : ReaderC.ramsey = ramsey := by
  funext s t; unfold ReaderC.ramsey ramsey; congr 1; ext n; exact prop_C s t n

theorem A_bounds : (type_of% @OAI.SharpRamseyFive.main) → (type_of% @ReaderA.reading_bounds) := by
  rintro ⟨⟨C, hC, h⟩, -⟩
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨t₀, ht⟩ := h ε hε
  rw [rA]
  exact eventually_atTop.mpr ⟨t₀, ht⟩

theorem A_limit : (type_of% @OAI.SharpRamseyFive.main) → (type_of% @ReaderA.reading_limit) := by
  rintro ⟨-, h⟩
  rw [rA]; exact h

theorem B_bounds : (type_of% @OAI.SharpRamseyFive.main) → (type_of% @ReaderB.reading_ramsey5_bounds) := by
  rintro ⟨⟨C, hC, h⟩, -⟩
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨t₀, ht⟩ := h ε hε
  rw [rB]
  refine eventually_atTop.mpr ⟨t₀, fun t htt => ?_⟩
  obtain ⟨h1, h2⟩ := ht t htt
  exact ⟨h1, by rw [← mul_div_assoc]; exact h2⟩

theorem B_limit : (type_of% @OAI.SharpRamseyFive.main) → (type_of% @ReaderB.reading_ramsey5_limit) := by
  rintro ⟨-, h⟩
  rw [rB]; exact h

theorem C_bounds : (type_of% @OAI.SharpRamseyFive.main) → (type_of% @ReaderC.reading_ramsey5_bound) := by
  rintro ⟨⟨C, hC, h⟩, -⟩
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨t₀, ht⟩ := h ε hε
  rw [rC]
  exact eventually_atTop.mpr ⟨t₀, ht⟩

theorem C_limit : (type_of% @OAI.SharpRamseyFive.main) → (type_of% @ReaderC.reading_ramsey5_limit) := by
  rintro ⟨-, h⟩
  rw [rC]; exact h

end TargetO.Ramsey5

#print axioms TargetO.Ramsey5.A_bounds
#print axioms TargetO.Ramsey5.A_limit
#print axioms TargetO.Ramsey5.B_bounds
#print axioms TargetO.Ramsey5.B_limit
#print axioms TargetO.Ramsey5.C_bounds
#print axioms TargetO.Ramsey5.C_limit
