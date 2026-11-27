import Mathlib
import Readings.Littlewood
import ComparatorChallenges.AsymptoticallyMinimalLittlewood

/-! # Target O, family O15 (real Littlewood polynomials): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped. Closed: the "Equivalently" form of every reader
(frozen ⇒ reading). Not closed: the "lim m_N = 1" forms; they add the lower bound m_N ≥ 1 ("Orthogonality
gives ‖P‖₂² = N"), which the source states as known and which no frozen statement carries. -/

namespace TargetO.Littlewood

theorem B_equiv : (type_of% @OAI.AsymptoticallyMinimalLittlewood.main) →
    (type_of% @ReaderB.reading_littlewood_equiv) := by
  intro h η hη
  obtain ⟨N₀, -, hN⟩ := h η hη
  refine ⟨N₀, fun N hN0 => ?_⟩
  obtain ⟨ε, hs, hb⟩ := hN N hN0
  exact ⟨ε, fun k => (hs k).symm, hb⟩

theorem A_equiv : (type_of% @OAI.AsymptoticallyMinimalLittlewood.main) →
    (type_of% @ReaderA.ReadingO15.reading_O15_equiv) := by
  intro h η hη
  obtain ⟨N₀, -, hN⟩ := h η hη
  refine ⟨N₀, fun N hN0 => ?_⟩
  obtain ⟨ε, hs, hb⟩ := hN N hN0
  refine ⟨fun k => if ε k = 1 then 1 else -1, fun z hz => ?_⟩
  have e : ∀ k, (((if ε k = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) : ℂ) = (ε k : ℂ) := by
    intro k
    rcases hs k with h1 | h1
    · have : ε k ≠ 1 := by rw [h1]; norm_num
      rw [if_neg this, h1]; simp
    · simp [h1]
  simp only [e]
  exact hb z hz

theorem C_equiv : (type_of% @OAI.AsymptoticallyMinimalLittlewood.main) →
    (type_of% @ReaderC.ReadingC.reading_littlewood_equiv) := by
  intro h η hη
  obtain ⟨N₀, -, hN⟩ := h η hη
  refine ⟨N₀, fun N hN0 => ?_⟩
  obtain ⟨ε, hs, hb⟩ := hN N hN0
  refine ⟨fun k => if hk : k < N then ε ⟨k, hk⟩ else 1, fun k hk => ?_, fun z hz => ?_⟩
  · simp only [hk, dite_true]; exact (hs ⟨k, hk⟩).symm
  · have := hb z hz
    unfold OAI.AsymptoticallyMinimalLittlewood.littlewoodValue at this
    rw [Finset.sum_range (fun k => (((if hk : k < N then ε ⟨k, hk⟩ else 1 : ℝ)) : ℂ) * z ^ k)]
    simpa using this

end TargetO.Littlewood

#print axioms TargetO.Littlewood.A_equiv
#print axioms TargetO.Littlewood.B_equiv
#print axioms TargetO.Littlewood.C_equiv
