import Mathlib
import Readings.Rokhlin
import ComparatorChallenges.Rokhlin

/-! # Target O, family O43 (Rokhlin's multiple mixing): closures (run 2026-11-27T1317Z).
Frozen statement taken with `type_of%`, never retyped. Closed: reader A's explicit form of Theorem 1.1 (gaps
n : Fin j → ℕ, positive, min → ∞; mixing along `comap |·| atTop`), from the frozen `mixing_all_finite_orders`
(gaps in ℕ+ along `atTop`; mixing along `comap natAbs atTop`). -/

namespace TargetO.Rokhlin

open MeasureTheory Filter Topology

universe u

theorem abs_le_natAbs : comap Int.natAbs (atTop : Filter ℕ) ≤ comap (fun n : ℤ => |n|) atTop := by
  have : (fun n : ℤ => |n|) = (fun m : ℕ => (m : ℤ)) ∘ Int.natAbs := funext fun n => Int.abs_eq_natAbs n
  rw [this, ← comap_comap]
  exact comap_mono tendsto_natCast_atTop_atTop.le_comap

/-- Gaps as positive naturals. -/
def toGaps {j : ℕ} (n : Fin j → ℕ) : Fin j → ℕ+ := fun i => Nat.toPNat' (n i)

theorem toGaps_tendsto (j : ℕ) : Tendsto (@toGaps j) (ReaderA.minAtTop j) atTop := by
  rw [tendsto_atTop]
  intro g0
  refine mem_iInf_of_mem (∑ i, (g0 i : ℕ)) (mem_principal.2 ?_)
  rintro n ⟨hpos, hN⟩ i
  show g0 i ≤ Nat.toPNat' (n i)
  rw [← PNat.coe_le_coe, Nat.toPNat'_coe, if_pos (hpos i)]
  exact (Finset.single_le_sum (fun l _ => Nat.zero_le _) (Finset.mem_univ i)).trans (hN i)

theorem layout_eq {j : ℕ} (n : Fin j → ℕ) (hpos : ∀ i, 0 < n i) (i : Fin (j + 1)) :
    ((OAI.Rokhlin.layoutTime (k := j + 1) (toGaps n) i : ℕ) : ℤ) = ReaderA.partialSum n i := by
  unfold OAI.Rokhlin.layoutTime ReaderA.partialSum
  rw [Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl (fun l _ => ?_)
  split_ifs <;> simp [toGaps, Nat.toPNat'_coe, hpos l]

theorem A_thm (H : type_of% @OAI.Rokhlin.mixing_all_finite_orders.{u}) :
    type_of% @ReaderA.reading_thm_1_1.{u} := by
  intro Ω _ μ _ T hT hmix j hj A hA
  have hmix' : OAI.Rokhlin.IsMixing μ T := fun A B hA hB =>
    (hmix A B hA hB).mono_left abs_le_natAbs
  have h := H μ T hT hmix' (j + 1) (by omega) A hA
  have h2 := h.comp (toGaps_tendsto j)
  refine h2.congr' ?_
  refine mem_iInf_of_mem 0 (mem_principal.2 ?_)
  rintro n ⟨hpos, -⟩
  show μ _ = μ _
  congr 1
  refine Set.iInter_congr (fun i => ?_)
  show _ ⁻¹' A i = _ ⁻¹' A i
  unfold ReaderA.tIter
  rw [layout_eq n hpos i]
  rfl

end TargetO.Rokhlin

#print axioms TargetO.Rokhlin.A_thm
