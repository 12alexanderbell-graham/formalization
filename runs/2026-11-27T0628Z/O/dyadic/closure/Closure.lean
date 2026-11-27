import Mathlib
import Readings.Dyadic
import ComparatorChallenges.DyadicAvoidance

/-! # Target O, family O16 (dyadic case of the Erdős similarity conjecture): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped. Direction frozen ⇒ reading. -/

open Set MeasureTheory

namespace TargetO.Dyadic

theorem pt (n : ℕ) : OAI.Problem310.dyadicPoint n = (2 : ℝ) ^ (-(n : ℤ)) := by
  unfold OAI.Problem310.dyadicPoint; rw [zpow_neg, zpow_natCast, inv_pow]

theorem core (h : (type_of% @OAI.Problem310.dyadic_affine_avoidance)) (η : ℝ) (h0 : 0 < η) (h1 : η < 1) :
    ∃ E : Set ℝ, IsCompact E ∧ E ⊆ Icc (0 : ℝ) 1 ∧ ENNReal.ofReal (1 - η) < volume E ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x + s * (2 : ℝ) ^ (-(n : ℤ)) ∉ E := by
  obtain ⟨E, hsub, hc, hv, hav⟩ := h η h0 h1
  refine ⟨E, hc, hsub, hv, fun x s hs => ?_⟩
  obtain ⟨n, hn, hnot⟩ := hav x s hs
  exact ⟨n, hn, by rwa [← pt]⟩

theorem A_main : (type_of% @OAI.Problem310.dyadic_affine_avoidance) →
    (type_of% @ReaderA.ReadingO16.reading_O16) := by
  intro h η hη
  obtain ⟨E, hc, hsub, hv, hav⟩ := core h η hη.1 hη.2
  refine ⟨E, hc, hsub, hv, fun x s hs hcopy => ?_⟩
  obtain ⟨n, hn, hnot⟩ := hav x s hs
  exact hnot (hcopy ⟨_, ⟨n, hn, rfl⟩, rfl⟩)

theorem A_equiv : (type_of% @OAI.Problem310.dyadic_affine_avoidance) →
    (type_of% @ReaderA.ReadingO16.reading_O16_equiv) :=
  fun h η hη => core h η hη.1 hη.2

theorem B_main : (type_of% @OAI.Problem310.dyadic_affine_avoidance) →
    (type_of% @ReaderB.reading_dyadic_copy) := by
  intro h η h0 h1
  obtain ⟨E, hc, hsub, hv, hav⟩ := core h η h0 h1
  refine ⟨E, hc, hsub, hv, fun x s hs hcopy => ?_⟩
  obtain ⟨n, hn, hnot⟩ := hav x s hs
  exact hnot (hcopy ⟨_, ⟨n, hn, rfl⟩, rfl⟩)

theorem B_equiv : (type_of% @OAI.Problem310.dyadic_affine_avoidance) →
    (type_of% @ReaderB.reading_dyadic_equiv) :=
  fun h η h0 h1 => core h η h0 h1

theorem C_main : (type_of% @OAI.Problem310.dyadic_affine_avoidance) →
    (type_of% @ReaderC.ReadingC.reading_dyadic_main) := by
  intro h η h0 h1
  obtain ⟨E, hc, hsub, hv, hav⟩ := core h η h0 h1
  refine ⟨E, hc, hsub, hv, fun x s hs hcopy => ?_, hav⟩
  obtain ⟨n, hn, hnot⟩ := hav x s hs
  exact hnot (hcopy ⟨_, ⟨n, hn, rfl⟩, rfl⟩)

end TargetO.Dyadic

#print axioms TargetO.Dyadic.A_main
#print axioms TargetO.Dyadic.A_equiv
#print axioms TargetO.Dyadic.B_main
#print axioms TargetO.Dyadic.B_equiv
#print axioms TargetO.Dyadic.C_main
