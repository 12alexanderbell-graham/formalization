import Mathlib
import Readings.Noncoord
import ComparatorChallenges.AbhyankarSathaye

/-! # Target O, family O10 (explicit noncoordinate polynomial): closures (run 2026-11-27T0628Z).
Frozen statement (Corollary 1.2 only) taken with `type_of%`, never retyped. Not closed: the readings of
Theorem 1.1 about the explicit F (quotient ≅ ℂ^[3]; ∇F(P) = 0 as `pderiv`; F not a coordinate) — no frozen
statement names F. The gradient claim is certified separately on the real polynomial function
(`noncoord/check/Gradient.lean`). -/

namespace TargetO.Noncoord

theorem A_cor : (type_of% @OAI.AbhyankarSathaye.exists_noncoordinate_polynomial) ↔
    (type_of% @ReaderA.ReadingO10A.reading_cor) := by
  constructor
  · intro h n hn
    obtain ⟨F, hq, hnc⟩ := h n hn
    exact ⟨F, hq, fun ⟨e, i, he⟩ => hnc ⟨e, i, he⟩⟩
  · intro h n hn
    obtain ⟨F, hq, hnc⟩ := h n hn
    exact ⟨F, hq, fun ⟨e, i, he⟩ => hnc ⟨e, i, he⟩⟩

theorem B_cor : (type_of% @OAI.AbhyankarSathaye.exists_noncoordinate_polynomial) →
    (type_of% @ReaderB.ReadingB.reading_cor) := by
  intro h n hn
  obtain ⟨F, hq, hnc⟩ := h n hn
  exact ⟨F, hq, fun ⟨e, he⟩ => hnc ⟨e, _, he⟩⟩

theorem C_cor : (type_of% @OAI.AbhyankarSathaye.exists_noncoordinate_polynomial) ↔
    (type_of% @ReaderC.O10Reading.reading_cor) := by
  constructor
  · intro h n hn
    obtain ⟨F, hq, hnc⟩ := h n hn
    exact ⟨F, hq, fun ⟨e, i, he⟩ => hnc ⟨e, i, he⟩⟩
  · intro h n hn
    obtain ⟨F, hq, hnc⟩ := h n hn
    exact ⟨F, hq, fun ⟨e, i, he⟩ => hnc ⟨e, i, he⟩⟩

/-- Reader C's sanity identity x² + y³ = h·s (the source's divisibility claim), proved outright. -/
theorem C_identity : (type_of% @OAI.AbhyankarSathaye.exists_noncoordinate_polynomial) →
    (type_of% @ReaderC.O10Reading.reading_identity) := by
  intro _
  unfold ReaderC.O10Reading.xX ReaderC.O10Reading.yY ReaderC.O10Reading.sS
  ring

end TargetO.Noncoord

#print axioms TargetO.Noncoord.A_cor
#print axioms TargetO.Noncoord.B_cor
#print axioms TargetO.Noncoord.C_cor
#print axioms TargetO.Noncoord.C_identity
