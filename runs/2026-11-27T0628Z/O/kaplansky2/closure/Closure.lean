import Mathlib
import Readings.Kaplansky2
import ComparatorChallenges.KaplanskyFinitelyPresented

/-! # Target O, family O3 (Kaplansky direct finiteness, characteristic two): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped. Not closed: every
reader's `reading_gottschalk` (the cellular-automaton consequence the manuscript states as proved has
no Lean statement in this family; the odd-characteristic family's challenge has one). -/

namespace TargetO.Kaplansky2

theorem A_reading : (type_of% @OAI.KaplanskyCounterexample.finitelyPresented_counterexample) ↔
    (type_of% @ReaderA.BlindReadingA.Kaplansky.reading) := by
  constructor
  · rintro ⟨K, hF, hFt, hc, G, hG, hfp, ⟨ℓ, hℓ, ho, g, hg⟩, a, b, hab, hba⟩
    exact ⟨K, hF, inferInstance, hc, G, hG, hfp, ⟨g, ℓ, hℓ, ho, hg⟩, a, b, hab, hba⟩
  · rintro ⟨K, hF, hFi, hc, G, hG, hfp, ⟨g, p, hp, ho, hg⟩, a, b, hab, hba⟩
    exact ⟨K, hF, Fintype.ofFinite K, hc, G, hG, hfp, ⟨p, hp, ho, g, hg⟩, a, b, hab, hba⟩

theorem B_reading : (type_of% @OAI.KaplanskyCounterexample.finitelyPresented_counterexample) ↔
    (type_of% @ReaderB.reading) := by
  constructor
  · rintro ⟨K, hF, hFt, hc, G, hG, hfp, ⟨ℓ, hℓ, ho, g, hg⟩, a, b, hab, hba⟩
    refine ⟨K, hF, hFt, hc, G, hG, hfp, ⟨g, hg ▸ hℓ, ?_⟩, a, b, hab, hba⟩
    rw [hg]; rintro rfl; exact (by decide : ¬ Odd 2) ho
  · rintro ⟨K, hF, hFt, hc, G, hG, hfp, ⟨g, hp, h2⟩, a, b, hab, hba⟩
    exact ⟨K, hF, hFt, hc, G, hG, hfp, ⟨orderOf g, hp, hp.odd_of_ne_two h2, g, rfl⟩, a, b, hab, hba⟩

theorem C_reading : (type_of% @OAI.KaplanskyCounterexample.finitelyPresented_counterexample) ↔
    (type_of% @ReaderC.reading) := by
  constructor
  · rintro ⟨K, hF, hFt, hc, G, hG, hfp, ⟨ℓ, hℓ, ho, g, hg⟩, a, b, hab, hba⟩
    exact ⟨K, hF, inferInstance, hc, G, hG, hfp, ⟨g, ℓ, hℓ, ho, hg⟩, a, b, hab, hba⟩
  · rintro ⟨K, hF, hFi, hc, G, hG, hfp, ⟨g, p, hp, ho, hg⟩, a, b, hab, hba⟩
    exact ⟨K, hF, Fintype.ofFinite K, hc, G, hG, hfp, ⟨p, hp, ho, g, hg⟩, a, b, hab, hba⟩

end TargetO.Kaplansky2

#print axioms TargetO.Kaplansky2.A_reading
#print axioms TargetO.Kaplansky2.B_reading
#print axioms TargetO.Kaplansky2.C_reading
