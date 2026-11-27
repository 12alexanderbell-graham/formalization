import Mathlib
import Readings.kadisonkastler
import ComparatorChallenges.StrongKadisonKastler

/-! # Target O, family O55 (strong Kadison–Kastler stability): closures (run 2026-11-27T1428Z).
Frozen statement `universal_strong_stability` (distance `Metric.hausdorffDist` of the unit balls), taken with
`type_of%`, never retyped. The readers wrote the text's max of two sup-inf terms over the unit balls; the frozen
Hausdorff distance is proved at most that (each frozen `infDist` is at most the reader's infimum, which is at most
the reader's supremum), so a reader's hypothesis `d(M, N) < δ` gives the frozen one. Closed: readers A and B.
Reader C (a `StarSubalgebra` equal to its bicommutant, `sSup`/`sInf` of images) is not closed here. -/

namespace TargetO.KK

open OAI.KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem zero_mem_ball (M : VonNeumannAlgebra H) : (0 : H →L[ℂ] H) ∈ unitBall M := ⟨zero_mem M, by simp⟩

/-- The frozen distance is at most any `r ≥ 0` that bounds both one-sided real `infDist`s. -/
theorem frozen_le (M N : VonNeumannAlgebra H) (r : ℝ)
    (h1 : ∀ x ∈ unitBall M, ⨅ y : unitBall N, ‖x - (y : H →L[ℂ] H)‖ ≤ r)
    (h2 : ∀ y ∈ unitBall N, ⨅ x : unitBall M, ‖(x : H →L[ℂ] H) - y‖ ≤ r) (hr : 0 ≤ r) :
    kkDistance M N ≤ r := by
  have hN : Nonempty (unitBall N) := ⟨⟨0, zero_mem_ball N⟩⟩
  have hM : Nonempty (unitBall M) := ⟨⟨0, zero_mem_ball M⟩⟩
  refine Metric.hausdorffDist_le_of_infDist hr (fun x hx => ?_) (fun y hy => ?_)
  · refine le_trans ?_ (h1 x hx)
    refine le_ciInf fun y => ?_
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem y.2
  · refine le_trans ?_ (h2 y hy)
    refine le_ciInf fun x => ?_
    rw [← dist_eq_norm, dist_comm]; exact Metric.infDist_le_dist_of_mem x.2

theorem inner_bdd (M N : VonNeumannAlgebra H) :
    BddAbove (Set.range fun x : unitBall M => ⨅ y : unitBall N, ‖(x : H →L[ℂ] H) - y‖) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  refine (ciInf_le ⟨0, fun _ ⟨y, hy⟩ => hy ▸ norm_nonneg _⟩ ⟨0, zero_mem_ball N⟩).trans ?_
  simpa using x.2.2

theorem inner_bdd' (M N : VonNeumannAlgebra H) :
    BddAbove (Set.range fun y : unitBall N => ⨅ x : unitBall M, ‖(x : H →L[ℂ] H) - y‖) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨y, rfl⟩
  refine (ciInf_le ⟨0, fun _ ⟨x, hx⟩ => hx ▸ norm_nonneg _⟩ ⟨0, zero_mem_ball M⟩).trans ?_
  simpa [norm_neg] using y.2.2

theorem frozen_le_A (M N : VonNeumannAlgebra H) : kkDistance M N ≤ ReaderA.kkDist M N := by
  have hM : Nonempty (unitBall M) := ⟨⟨0, zero_mem_ball M⟩⟩
  have hN : Nonempty (unitBall N) := ⟨⟨0, zero_mem_ball N⟩⟩
  have h0 : 0 ≤ ReaderA.kkDist M N := by
    refine le_trans ?_ (le_max_left _ _)
    exact Real.iSup_nonneg fun x => Real.iInf_nonneg fun y => norm_nonneg _
  refine frozen_le M N _ (fun x hx => ?_) (fun y hy => ?_) h0
  · exact (le_ciSup (inner_bdd M N) (⟨x, hx⟩ : unitBall M)).trans (le_max_left _ _)
  · exact (le_ciSup (inner_bdd' M N) (⟨y, hy⟩ : unitBall N)).trans (le_max_right _ _)

theorem frozen_le_B (M N : VonNeumannAlgebra H) : kkDistance M N ≤ ReaderB.kkDist M N := by
  have := frozen_le_A M N
  exact this

theorem A_thm (H0 : type_of% @universal_strong_stability.{u}) :
    type_of% @ReaderA.reading_strong_kadison_kastler.{u} := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := H0 ε hε
  refine ⟨δ, hδ, fun H _ _ _ M N hd => ?_⟩
  obtain ⟨v, hv, hn⟩ := h H M N (lt_of_le_of_lt (frozen_le_A M N) hd)
  exact ⟨v, v.2, hv, hn⟩

theorem B_thm (H0 : type_of% @universal_strong_stability.{u}) :
    type_of% @ReaderB.readingKadisonKastler.{u} := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := H0 ε hε
  refine ⟨δ, hδ, fun H _ _ _ M N hd => ?_⟩
  obtain ⟨v, hv, hn⟩ := h H M N (lt_of_le_of_lt (frozen_le_B M N) hd)
  exact ⟨v, hv, hn⟩

end TargetO.KK

#print axioms TargetO.KK.A_thm
#print axioms TargetO.KK.B_thm
