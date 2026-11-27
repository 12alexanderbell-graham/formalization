import Mathlib
import Readings.ListHadwiger
import ComparatorChallenges.ListHadwiger

/-! # Target O, family O42 (linear list Hadwiger): closures (run 2026-11-27T1317Z).
Frozen statement taken with `type_of%`, never retyped. Closed: every reader's Theorem 1.1. Non-vacuity of the
frozen `listChromaticNumber` (an `sInf`): lists of size ≥ |V| over any color type are colorable (Hall), so the set
is nonempty and the `sInf` is a genuine minimum, proved here. The frozen `hadwigerNumber` (an `sSup`) is a genuine
maximum: a `K_t` minor has `t ≤ |V|`. -/

namespace TargetO.ListHadwiger

open OAI.LinearListHadwiger

variable {V : Type} [Fintype V]

theorem choosable_card (G : SimpleGraph V) : Choosable G (Fintype.card V) := by
  classical
  intro Color L hL
  obtain ⟨f, hf, hfL⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective L).1 (by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · calc s.card ≤ Fintype.card V := Finset.card_le_univ s
        _ ≤ (L v).card := hL v
        _ ≤ (s.biUnion L).card := Finset.card_le_card (Finset.subset_biUnion_of_mem L hv))
  exact ⟨f, hfL, fun u v huv h => G.ne_of_adj huv (hf h)⟩

theorem frozen_list_mem (G : SimpleGraph V) : Choosable G (listChromaticNumber G) :=
  Nat.sInf_mem (s := {k : ℕ | Choosable G k}) ⟨_, choosable_card G⟩

theorem minor_le_card (G : SimpleGraph V) (t : ℕ) (h : HasCliqueMinor G t) :
    t ≤ Fintype.card V := by
  obtain ⟨B, hc, hd, -⟩ := h
  have hne : ∀ i, (B i).Nonempty := fun i => by
    obtain ⟨⟨x, hx⟩⟩ := (hc i).nonempty
    exact ⟨x, hx⟩
  choose f hf using hne
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne'
    exact Set.disjoint_left.1 (hd i j hne') (hf i) (hij ▸ hf j)
  simpa using Fintype.card_le_of_injective f hinj

theorem bdd (G : SimpleGraph V) : BddAbove {t : ℕ | HasCliqueMinor G t} :=
  ⟨Fintype.card V, fun t ht => minor_le_card G t ht⟩

theorem minor_zero (G : SimpleGraph V) : HasCliqueMinor G 0 :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem le_frozen (G : SimpleGraph V) {t : ℕ} (h : HasCliqueMinor G t) : t ≤ hadwigerNumber G :=
  le_csSup (bdd G) h

theorem frozen_mem (G : SimpleGraph V) : HasCliqueMinor G (hadwigerNumber G) :=
  Nat.sSup_mem ⟨0, minor_zero G⟩ (bdd G)

theorem nonempty_of_connected {G : SimpleGraph V} {S : Set V} (h : (G.induce S).Connected) :
    S.Nonempty := by
  obtain ⟨⟨x, hx⟩⟩ := h.nonempty
  exact ⟨x, hx⟩

/-! Reader A. -/

theorem A_hadwiger (G : SimpleGraph V) : hadwigerNumber G ≤ ReaderA.hadwiger G := by
  classical
  unfold ReaderA.hadwiger
  apply Nat.le_findGreatest (minor_le_card G _ (frozen_mem G))
  obtain ⟨B, hc, hd, ha⟩ := frozen_mem G
  exact ⟨B, hd, hc, ha⟩

theorem A_list (G : SimpleGraph V) : ReaderA.listChromatic G ≤ listChromaticNumber G := by
  classical
  unfold ReaderA.listChromatic
  apply Nat.find_min'
  intro L hL
  obtain ⟨c, hc, hp⟩ := frozen_list_mem G ℕ L hL
  exact ⟨c, hc, fun u v huv => hp huv⟩

theorem A_thm (H : type_of% @main_theorem) : type_of% @ReaderA.reading_thm_1_1 := by
  obtain ⟨C, hC, hb⟩ := H
  refine ⟨C, hC, fun W _ _ G => ?_⟩
  calc ReaderA.listChromatic G ≤ listChromaticNumber G := A_list G
    _ ≤ C * hadwigerNumber G := hb W G
    _ ≤ C * ReaderA.hadwiger G := Nat.mul_le_mul_left C (A_hadwiger G)

/-! Reader B. -/

theorem B_thm (H : type_of% @main_theorem) : type_of% @ReaderB.reading_thm_1_1 := by
  obtain ⟨C, hC, hb⟩ := H
  refine ⟨C, hC, fun W _ _ G ℓ h hℓ hh => ?_⟩
  have hℓ' : ℓ ≤ listChromaticNumber G := by
    by_contra hlt
    push_neg at hlt
    apply hℓ.2 _ hlt
    intro κ L hL
    obtain ⟨c, hc, hp⟩ := frozen_list_mem G κ L hL
    exact ⟨c, hc, fun u v huv => hp huv⟩
  have hh' : hadwigerNumber G ≤ h := by
    apply hh.2
    obtain ⟨B, hc, hd, ha⟩ := frozen_mem G
    exact ⟨B, fun i => nonempty_of_connected (hc i), hc, fun i j hij => hd i j hij, ha⟩
  calc ℓ ≤ listChromaticNumber G := hℓ'
    _ ≤ C * hadwigerNumber G := hb W G
    _ ≤ C * h := Nat.mul_le_mul_left C hh'

/-! Reader C. -/

theorem C_thm (H : type_of% @main_theorem) : type_of% @ReaderC.reading_thm_1_1 := by
  obtain ⟨C, hC, hb⟩ := H
  refine ⟨C, hC, fun W _ _ G => ?_⟩
  have hl : ReaderC.listChromatic G ≤ listChromaticNumber G := by
    apply Nat.sInf_le
    intro L hL
    obtain ⟨c, hc, hp⟩ := frozen_list_mem G ℕ L hL
    exact ⟨c, hc, fun u v huv => hp huv⟩
  have hh : hadwigerNumber G ≤ ReaderC.hadwiger G := by
    apply le_csSup
    · refine ⟨Fintype.card W, fun t ⟨B, _, hd, hc, ha⟩ => minor_le_card G t ⟨B, hc, hd, ha⟩⟩
    · obtain ⟨B, hc, hd, ha⟩ := frozen_mem G
      exact ⟨B, fun i => nonempty_of_connected (hc i), hd, hc, ha⟩
  calc ReaderC.listChromatic G ≤ listChromaticNumber G := hl
    _ ≤ C * hadwigerNumber G := hb W G
    _ ≤ C * ReaderC.hadwiger G := Nat.mul_le_mul_left C hh

end TargetO.ListHadwiger

#print axioms TargetO.ListHadwiger.A_thm
#print axioms TargetO.ListHadwiger.B_thm
#print axioms TargetO.ListHadwiger.C_thm
