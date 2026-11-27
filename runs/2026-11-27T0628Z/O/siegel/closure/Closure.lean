import Mathlib
import Readings.Siegel
import ComparatorChallenges.SiegelZeros

/-! # Target O, family O28 (uniform exclusion of Landau–Siegel zeros): closures (run 2026-11-27T0628Z).
Frozen statement taken with `type_of%`, never retyped: `exists_absolute_real_zero_gap` — some c > 0 such that for
q ≥ 3, every primitive χ ≠ 1 mod q with real values, every real zero β ∈ (0, 1) of `χ.LFunction` has
c ≤ (1 − β) log q. Closed (frozen ⇒ reading): every reader's Theorem 1.1 (the same statement up to argument order),
and reader A's conductor form (a primitive character's conductor is its modulus). `LFunction` is pinned as the
continuation of the Dirichlet series in target R (`R/closure/Pins.lean`). -/

namespace TargetO.Siegel

theorem A_thm : (type_of% @OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap) →
    (type_of% @ReaderA.reading_thm_1_1) := by
  rintro ⟨c, hc, h⟩
  exact ⟨c, hc, fun q _ χ hq hp h1 hr β h0 h1' hz => h q hq χ hp h1 hr β h0 h1' hz⟩

theorem A_conductor : (type_of% @OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap) →
    (type_of% @ReaderA.reading_thm_1_1_conductor) := by
  rintro ⟨c, hc, h⟩
  refine ⟨c, hc, fun N _ χ hp h1 hr hq β h0 h1' hz => ?_⟩
  have hc' : χ.conductor = N := hp
  rw [hc'] at hq ⊢
  exact h N hq χ hp h1 hr β h0 h1' hz

theorem B_thm : (type_of% @OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap) →
    (type_of% @ReaderB.readingMain) := by
  rintro ⟨c, hc, h⟩
  exact ⟨c, hc, fun q _ hq χ hp h1 hr β h0 h1' hz => h q hq χ hp h1 hr β h0 h1' hz⟩

theorem C_thm : (type_of% @OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap) →
    (type_of% @ReaderC.reading_thm_1_1_landau_siegel) := by
  rintro ⟨c, hc, h⟩
  exact ⟨c, hc, fun q _ χ hp h1 hq hr β h0 h1' hz => h q hq χ hp h1 hr β h0 h1' hz⟩

end TargetO.Siegel

#print axioms TargetO.Siegel.A_thm
#print axioms TargetO.Siegel.A_conductor
#print axioms TargetO.Siegel.B_thm
#print axioms TargetO.Siegel.C_thm
