import Mathlib
import Readings.kadisonkastler
import ComparatorChallenges.StrongKadisonKastler

/-! # Target O, family O55 (strong Kadison–Kastler stability): closure of reader C (run 2026-11-27T1628Z).

Frozen statement `OAI.KadisonKastler.universal_strong_stability`, taken with `type_of%`, never retyped. Readers A
and B were closed in run 2026-11-27T1428Z (`runs/2026-11-27T1428Z/O/kadisonkastler/closure/Closure.lean`).

Reader C wrote a von Neumann algebra concretely: a `StarSubalgebra ℂ (H →L[ℂ] H)` equal to its double commutant,
with its own commutant `commSet`. `commSet` is, by definition, Mathlib's `Set.centralizer` (proved by `rfl`), so
reader C's algebra *is* a Mathlib `VonNeumannAlgebra` (`toVNA`), the frozen type, with the same carrier and the same
unit ball. Reader C's distance is the text's max of two sup–inf terms written with `sSup`/`sInf` over images of the
unit balls (all sets nonempty and bounded, as the reader noted); the frozen Hausdorff distance is proved at most
that (`frozen_le_C`), so a reader's hypothesis `d(M, N) < δ` gives the frozen one. The reader's extra hypotheses
`1 ∈ M`, `1 ∈ N` are not used; reader C's `H : Type` is the frozen statement at universe 0. -/

namespace TargetO.KKC

open OAI.KadisonKastler

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commSet_eq (S : Set (H →L[ℂ] H)) : ReaderC.commSet H S = Set.centralizer S := rfl

/-- Reader C's von Neumann algebra as Mathlib's (the frozen statement's) `VonNeumannAlgebra`. -/
def toVNA (M : StarSubalgebra ℂ (H →L[ℂ] H)) (hM : ReaderC.IsVNA H M) : VonNeumannAlgebra H :=
  { M with centralizer_centralizer' := hM }

theorem coe_toVNA (M : StarSubalgebra ℂ (H →L[ℂ] H)) (hM : ReaderC.IsVNA H M) :
    ((toVNA M hM : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) := rfl

theorem unitBall_toVNA (M : StarSubalgebra ℂ (H →L[ℂ] H)) (hM : ReaderC.IsVNA H M) :
    unitBall (toVNA M hM) = ReaderC.unitBall H M := rfl

theorem zero_mem_C (M : StarSubalgebra ℂ (H →L[ℂ] H)) : (0 : H →L[ℂ] H) ∈ ReaderC.unitBall H M :=
  ⟨zero_mem M, by simp⟩

/-- Reader C's one-sided infimum is at most `‖x‖` (take `y = 0`), and nonnegative. -/
theorem innerC_le (M N : StarSubalgebra ℂ (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    sInf ((fun y : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H N) ≤ ‖x‖ := by
  have hmem : ‖x - 0‖ ∈ (fun y : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H N := ⟨0, zero_mem_C N, rfl⟩
  have hbdd : BddBelow ((fun y : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H N) :=
    ⟨0, by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg _⟩
  exact (csInf_le hbdd hmem).trans (by rw [sub_zero])

theorem innerC_le' (M N : StarSubalgebra ℂ (H →L[ℂ] H)) (y : H →L[ℂ] H) :
    sInf ((fun x : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H M) ≤ ‖y‖ := by
  have hmem : ‖0 - y‖ ∈ (fun x : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H M := ⟨0, zero_mem_C M, rfl⟩
  have hbdd : BddBelow ((fun x : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H M) :=
    ⟨0, by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg _⟩
  exact (csInf_le hbdd hmem).trans (by rw [zero_sub, norm_neg])

theorem innerC_nonneg (S : Set (H →L[ℂ] H)) (g : (H →L[ℂ] H) → ℝ) (hg : ∀ y, 0 ≤ g y) :
    0 ≤ sInf (g '' S) :=
  Real.sInf_nonneg (by rintro _ ⟨y, _, rfl⟩; exact hg y)

theorem frozen_le_C (M N : StarSubalgebra ℂ (H →L[ℂ] H)) (hM : ReaderC.IsVNA H M) (hN : ReaderC.IsVNA H N) :
    kkDistance (toVNA M hM) (toVNA N hN) ≤ ReaderC.kkDist H M N := by
  set r := ReaderC.kkDist H M N
  have bdd1 : BddAbove ((fun x : H →L[ℂ] H => sInf ((fun y : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H N))
      '' ReaderC.unitBall H M) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (innerC_le M N x).trans hx.2
  have bdd2 : BddAbove ((fun y : H →L[ℂ] H => sInf ((fun x : H →L[ℂ] H => ‖x - y‖) '' ReaderC.unitBall H M))
      '' ReaderC.unitBall H N) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (innerC_le' M N y).trans hy.2
  have hr : 0 ≤ r := by
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_csSup bdd1 ⟨0, zero_mem_C M, rfl⟩)
    exact innerC_nonneg _ _ fun _ => norm_nonneg _
  refine Metric.hausdorffDist_le_of_infDist hr (fun x hx => ?_) (fun y hy => ?_)
  · rw [unitBall_toVNA] at hx
    refine le_trans ?_ ((le_csSup bdd1 ⟨x, hx, rfl⟩).trans (le_max_left _ _))
    refine le_csInf ⟨_, ⟨0, zero_mem_C N, rfl⟩⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    show _ ≤ ‖x - y‖
    rw [← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (by rw [unitBall_toVNA]; exact hy)
  · rw [unitBall_toVNA] at hy
    refine le_trans ?_ ((le_csSup bdd2 ⟨y, hy, rfl⟩).trans (le_max_right _ _))
    refine le_csInf ⟨_, ⟨0, zero_mem_C M, rfl⟩⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    show _ ≤ ‖x - y‖
    rw [← dist_eq_norm, dist_comm]
    exact Metric.infDist_le_dist_of_mem (by rw [unitBall_toVNA]; exact hx)

theorem C_thm (H0 : type_of% @universal_strong_stability.{0}) :
    type_of% @ReaderC.reading_strong_kk := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := H0 ε hε
  refine ⟨δ, hδ, fun H _ _ _ M N hM hN _ _ hd => ?_⟩
  obtain ⟨v, hv, hn⟩ := h H (toVNA M hM) (toVNA N hN) (lt_of_le_of_lt (frozen_le_C M N hM hN) hd)
  exact ⟨v, v.2, hv, hn⟩

theorem reading_C_closed : type_of% @ReaderC.reading_strong_kk :=
  C_thm (@universal_strong_stability.{0})

end TargetO.KKC

#print axioms TargetO.KKC.C_thm
#print axioms TargetO.KKC.reading_C_closed
