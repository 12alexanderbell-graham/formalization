import Mathlib
import Readings.seymour
import ComparatorChallenges.SeymourSecondNeighborhood

/-! # Target O, family O44 (Seymour's second-neighborhood conjecture): closures (run 2026-11-27T1428Z).
Frozen statement taken with `type_of%`, never retyped (at universe 0, the readers' universe). Closed in both
directions for every reader: the frozen theorem implies each reader's Theorem 1.1, and each reader's Theorem 1.1
implies the frozen theorem, so the four statements are equivalent on `Type`. The triangle theorems of readers A
and B are not readings (the brief's excerpt stopped before that sentence) and are not closed. -/

namespace TargetO.Seymour

open OAI.SeymourSecondNeighborhood

/-- The frozen first neighbourhood as a set. -/
theorem first_eq {V : Type} [Fintype V] [DecidableEq V] (r : V → V → Prop) (v : V) :
    ((firstNeighbors r v : Finset V) : Set V) = {u | r v u} := by
  ext u; simp [firstNeighbors]

theorem second_eq {V : Type} [Fintype V] [DecidableEq V] (r : V → V → Prop) (v : V) :
    ((secondNeighbors r v : Finset V) : Set V) =
      {w | w ∉ ({v} ∪ {u | r v u}) ∧ ∃ u, r v u ∧ r u w} := by
  ext w; simp [secondNeighbors, not_or, and_assoc]

theorem good_iff {V : Type} [Fintype V] [DecidableEq V] (r : V → V → Prop) (v : V) :
    GoodVertex r v ↔
      ({u | r v u} : Set V).ncard ≤ ({w | w ∉ ({v} ∪ {u | r v u}) ∧ ∃ u, r v u ∧ r u w} : Set V).ncard := by
  unfold GoodVertex
  rw [← second_eq, ← first_eq, Set.ncard_coe_finset, Set.ncard_coe_finset]

/-! Reader A (Mathlib `Digraph`). -/

theorem A_of_frozen (H : type_of% @exists_goodVertex.{0}) : type_of% @ReaderA.reading_thm_1_1 := by
  intro V _ _ G hG
  classical
  obtain ⟨v, hv⟩ := H G.Adj ⟨hG.1, fun h => hG.2 _ _ h⟩
  exact ⟨v, (good_iff _ v).1 hv⟩

theorem frozen_of_A (H : type_of% @ReaderA.reading_thm_1_1) : type_of% @exists_goodVertex.{0} := by
  intro V _ _ _ r hr
  obtain ⟨v, hv⟩ := H V ⟨r⟩ ⟨hr.loopless, fun u w h => hr.asymmetric h⟩
  exact ⟨v, (good_iff r v).2 hv⟩

/-! Reader B (own `OrientedGraph` structure). -/

theorem B_of_frozen (H : type_of% @exists_goodVertex.{0}) : type_of% @ReaderB.reading_seymour_second_neighborhood := by
  intro V _ _ G
  classical
  obtain ⟨v, hv⟩ := H G.adj ⟨G.loopless, fun h => G.no_opposite _ _ h⟩
  exact ⟨v, (good_iff _ v).1 hv⟩

theorem frozen_of_B (H : type_of% @ReaderB.reading_seymour_second_neighborhood) :
    type_of% @exists_goodVertex.{0} := by
  intro V _ _ _ r hr
  obtain ⟨v, hv⟩ := H V ⟨r, hr.loopless, fun u w h => hr.asymmetric h⟩
  exact ⟨v, (good_iff r v).2 hv⟩

/-! Reader C (`Finset` filters). -/

theorem C_of_frozen (H : type_of% @exists_goodVertex.{0}) : type_of% @ReaderC.reading_seymour_thm1_1 := by
  intro V _ _ adj hadj
  classical
  obtain ⟨v, hv⟩ := H adj ⟨hadj.1, fun h => hadj.2 _ _ h⟩
  refine ⟨v, ?_⟩
  have e1 : ReaderC.outN1 adj v = firstNeighbors adj v := by
    ext u; simp [ReaderC.outN1, firstNeighbors]
  have e2 : ReaderC.outN2 adj v = secondNeighbors adj v := by
    ext u; simp [ReaderC.outN2, secondNeighbors]
  rw [e1, e2]; exact hv

theorem frozen_of_C (H : type_of% @ReaderC.reading_seymour_thm1_1) : type_of% @exists_goodVertex.{0} := by
  intro V _ _ _ r hr
  classical
  obtain ⟨v, hv⟩ := H V r ⟨hr.loopless, fun u w h => hr.asymmetric h⟩
  refine ⟨v, ?_⟩
  have e1 : ReaderC.outN1 r v = firstNeighbors r v := by
    ext u; simp [ReaderC.outN1, firstNeighbors]
  have e2 : ReaderC.outN2 r v = secondNeighbors r v := by
    ext u; simp [ReaderC.outN2, secondNeighbors]
  unfold GoodVertex; rw [← e1, ← e2]; exact hv

/-! Non-vacuity and bite: the hypotheses are satisfiable (the 3-cycle is oriented), and orientation is needed:
on two vertices with arcs both ways, neither vertex is good. -/

theorem cycle3_oriented : IsOriented (fun a b : Fin 3 => b = a + 1) :=
  ⟨by decide, by decide⟩

theorem digon_no_good : ¬ ∃ v : Fin 2, GoodVertex (fun a b : Fin 2 => a ≠ b) v := by
  rintro ⟨v, hv⟩
  unfold GoodVertex at hv
  revert hv
  fin_cases v <;> simp [firstNeighbors, secondNeighbors] <;> decide

end TargetO.Seymour

#print axioms TargetO.Seymour.A_of_frozen
#print axioms TargetO.Seymour.frozen_of_A
#print axioms TargetO.Seymour.B_of_frozen
#print axioms TargetO.Seymour.frozen_of_B
#print axioms TargetO.Seymour.C_of_frozen
#print axioms TargetO.Seymour.frozen_of_C
#print axioms TargetO.Seymour.digon_no_good
