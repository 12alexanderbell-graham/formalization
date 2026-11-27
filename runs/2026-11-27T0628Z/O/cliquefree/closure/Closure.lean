import Mathlib
import Readings.CliqueFree
import ComparatorChallenges.CliqueFreeLog

/-! # Target O, family O11 (logarithmic independence bound for K_r-free graphs): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped. Direction frozen ⇒ reading:
the readers' own edge counts, clique-freeness and independence numbers are related to Mathlib's. -/

open scoped Classical

namespace TargetO.CliqueFree

theorem edge_card_eq {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

theorem avg_eq {V : Type} [Fintype V] (G : SimpleGraph V) :
    OAI.CliqueFreeLog.averageDegree G = 2 * (Nat.card G.edgeSet : ℝ) / (Fintype.card V : ℝ) := by
  unfold OAI.CliqueFreeLog.averageDegree
  rw [edge_card_eq]

theorem indep_witness {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ s.card = G.indepNum := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  exact ⟨s, hs.isIndepSet, hs.card_eq⟩

theorem B_thm : (type_of% @OAI.CliqueFreeLog.logarithmic_independence_bound) →
    (type_of% @ReaderB.reading) := by
  intro h r hr
  obtain ⟨c, hc, hb⟩ := h r hr
  refine ⟨c, hc, fun V _ G _ hfree havg => ?_⟩
  have e : ReaderB.avgDegree G = OAI.CliqueFreeLog.averageDegree G := by
    rw [avg_eq]; rfl
  rw [e] at havg ⊢
  obtain ⟨s, hs, hcard⟩ := indep_witness G
  exact ⟨s, hs, by rw [hcard]; exact hb G hfree havg⟩

theorem C_thm : (type_of% @OAI.CliqueFreeLog.logarithmic_independence_bound) →
    (type_of% @ReaderC.reading) := by
  intro h r hr
  obtain ⟨c, hc, hb⟩ := h r hr
  refine ⟨c, hc, fun V _ G _ hfree havg => ?_⟩
  have e : ReaderC.avgDeg G = OAI.CliqueFreeLog.averageDegree G := by
    rw [avg_eq, edge_card_eq]; rfl
  rw [e] at havg ⊢
  have hcf : G.CliqueFree r := fun t ht => hfree t ht.card_eq ht.isClique
  refine le_trans (hb G hcf havg) ?_
  obtain ⟨s, hs, hcard⟩ := indep_witness G
  rw [← hcard]
  exact_mod_cast Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ s), fun u hu v hv huv => hs hu hv huv⟩)

theorem A_thm : (type_of% @OAI.CliqueFreeLog.logarithmic_independence_bound) →
    (type_of% @ReaderA.O11Reading.reading) := by
  intro h r hr
  obtain ⟨c, hc, hb⟩ := h r hr
  refine ⟨c, hc, fun V _ G _ hfree havg => ?_⟩
  have hne : ReaderA.O11Reading.numEdges G = G.edgeFinset.card := by
    unfold ReaderA.O11Reading.numEdges
    congr 1; ext e; simp
  have e : ReaderA.O11Reading.avgDegree G = OAI.CliqueFreeLog.averageDegree G := by
    rw [avg_eq, edge_card_eq]; unfold ReaderA.O11Reading.avgDegree; rw [hne]
  rw [e] at havg ⊢
  have hcf : G.CliqueFree r := by
    intro t ht
    exact hfree ⟨t, ht.card_eq, fun x hx y hy hxy => ht.isClique hx hy hxy⟩
  have key := hb G hcf havg
  have key' : c * ((Fintype.card V : ℝ) * Real.log (OAI.CliqueFreeLog.averageDegree G) /
      OAI.CliqueFreeLog.averageDegree G) ≤ (G.indepNum : ℝ) := by
    refine le_trans (le_of_eq ?_) key; ring
  refine le_trans key' ?_
  obtain ⟨s, hs, hcard⟩ := indep_witness G
  rw [← hcard]
  exact_mod_cast Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
    ⟨Finset.mem_univ s, fun x hx y hy hxy => hs hx hy (by rintro rfl; exact G.irrefl hxy) hxy⟩)

end TargetO.CliqueFree

#print axioms TargetO.CliqueFree.A_thm
#print axioms TargetO.CliqueFree.B_thm
#print axioms TargetO.CliqueFree.C_thm
