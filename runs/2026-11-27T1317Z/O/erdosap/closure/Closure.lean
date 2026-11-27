import Mathlib
import Readings.ErdosAP
import ComparatorChallenges.ErdosReciprocal

/-! # Target O, family O40 (Erdős reciprocal sums): closures (run 2026-11-27T1317Z).
Frozen statement taken with `type_of%`, never retyped. Corollary 1.2 (divergent reciprocal sum ⇒ progressions of
every length): readers A (sum in ENNReal = ⊤), B and C (¬ Summable over the subtype) closed. Theorem 1.1 and its
threshold form (the quantitative bound) have no Lean statement; OpenAI's scope document says so. -/

namespace TargetO.ErdosAP

open OAI.Erdos3

/-- The frozen series is the subtype series of `1/a`, extended by zero. -/
theorem summable_iff (A : Set ℕ) :
    Summable (reciprocalTerm A) ↔ Summable (fun a : A => 1 / ((a : ℕ) : ℝ)) := by
  have h : reciprocalTerm A = A.indicator (fun n : ℕ => 1 / (n : ℝ)) := by
    funext n; classical
    simp [reciprocalTerm, Set.indicator]
  rw [h, ← summable_subtype_iff_indicator]
  rfl

theorem B_cor (H : type_of% @manuscriptReciprocalProgressionTheorem) :
    type_of% @ReaderB.readingReciprocal := by
  intro A _ hdiv k
  obtain ⟨a, d, hd, h⟩ := H A (fun hs => hdiv ((summable_iff A).1 hs)) k
  exact ⟨a, d, hd, h⟩

theorem C_cor (H : type_of% @manuscriptReciprocalProgressionTheorem) :
    type_of% @ReaderC.reading_ap_cor2 := by
  intro A _ hdiv k
  obtain ⟨a, d, hd, h⟩ := H A (fun hs => hdiv ((summable_iff A).1 hs)) k
  exact ⟨a, d, hd, h⟩

theorem A_cor (H : type_of% @manuscriptReciprocalProgressionTheorem) :
    type_of% @ReaderA.reading_cor_1_2 := by
  intro A hpos hdiv k
  refine H A (fun hs => ?_) k
  rw [summable_iff] at hs
  have hs' : Summable (fun a : A => (((a : ℕ) : NNReal))⁻¹) := by
    rw [← NNReal.summable_coe]
    simpa [one_div] using hs
  have hne := (ENNReal.tsum_coe_ne_top_iff_summable).2 hs'
  apply hne
  rw [← hdiv]
  refine tsum_congr (fun a => ?_)
  have : ((a : ℕ) : NNReal) ≠ 0 := by exact_mod_cast (hpos a a.2).ne'
  rw [ENNReal.coe_inv this]
  simp

end TargetO.ErdosAP

#print axioms TargetO.ErdosAP.A_cor
#print axioms TargetO.ErdosAP.B_cor
#print axioms TargetO.ErdosAP.C_cor
