import Mathlib
import Readings.Hadwiger
import ComparatorChallenges.HadwigerCounterexample

/-! # Target O, family O41 (Hadwiger counterexample): closures (run 2026-11-27T1317Z).
Frozen statements taken with `type_of%`, never retyped. Closed: every reader's "Hadwiger's conjecture is false"
from the frozen `not_hadwiger_conjecture`. The readers' clique-minor notions are the frozen one (B and C add
nonemptiness of branch sets, which connectedness already forces); the frozen `sSup` is a genuine maximum because a
`K_t` minor has `t ≤ |V|` (proved here). Not closed: the corollary's χ_f bounds (no Lean statement; OpenAI's scope
document says the fractional strengthening is outside). -/

namespace TargetO.Hadwiger

open OAI.LinearListHadwiger

variable {V : Type} [Fintype V]

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

theorem A_minor (G : SimpleGraph V) (t : ℕ) : ReaderA.HasCliqueMinor G t ↔ HasCliqueMinor G t := by
  constructor
  · rintro ⟨B, hd, hc, ha⟩; exact ⟨B, hc, hd, ha⟩
  · rintro ⟨B, hc, hd, ha⟩; exact ⟨B, hd, hc, ha⟩

theorem B_minor (G : SimpleGraph V) (t : ℕ) : ReaderB.HasCliqueMinor G t ↔ HasCliqueMinor G t := by
  constructor
  · rintro ⟨B, -, hc, hd, ha⟩; exact ⟨B, hc, fun i j hij => hd hij, ha⟩
  · rintro ⟨B, hc, hd, ha⟩
    refine ⟨B, fun i => ?_, hc, fun i j hij => hd i j hij, ha⟩
    obtain ⟨⟨x, hx⟩⟩ := (hc i).nonempty
    exact ⟨x, hx⟩

theorem C_minor (G : SimpleGraph V) (t : ℕ) :
    (∃ B, ReaderC.IsCliqueMinorModel G t B) ↔ HasCliqueMinor G t := by
  constructor
  · rintro ⟨B, -, hd, hc, ha⟩; exact ⟨B, hc, hd, ha⟩
  · rintro ⟨B, hc, hd, ha⟩
    refine ⟨B, fun i => ?_, hd, hc, ha⟩
    obtain ⟨⟨x, hx⟩⟩ := (hc i).nonempty
    exact ⟨x, hx⟩

/-- The frozen counterexample, with its vertex set nonempty. -/
theorem frozen_cex (H : type_of% @OAI.HadwigerCounterexample.not_hadwiger_conjecture) :
    ∃ m : ℕ, 0 < m ∧ ∃ G : SimpleGraph (Fin m), ¬ G.chromaticNumber ≤ (hadwigerNumber G : ℕ∞) := by
  by_contra hno
  push_neg at hno
  apply H
  intro m G
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : G.chromaticNumber = 0 := by
      rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]
    simp [this]
  · exact hno m hm G

theorem A_false (H : type_of% @OAI.HadwigerCounterexample.not_hadwiger_conjecture) :
    type_of% @ReaderA.reading_hadwiger_false := by
  intro hall
  obtain ⟨m, hm, G, hG⟩ := frozen_cex H
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h1 := hall (Fin m) G
  apply hG
  have hcol : G.Colorable (ReaderA.chromatic G) := by
    classical
    unfold ReaderA.chromatic
    exact Nat.find_spec _
  have hA : ReaderA.hadwiger G ≤ hadwigerNumber G := by
    classical
    apply le_frozen
    rw [← A_minor]
    unfold ReaderA.hadwiger
    exact Nat.findGreatest_spec (Nat.zero_le _) ((A_minor G 0).2 (minor_zero G))
  calc G.chromaticNumber ≤ (ReaderA.chromatic G : ℕ∞) := hcol.chromaticNumber_le
    _ ≤ (hadwigerNumber G : ℕ∞) := by exact_mod_cast h1.trans hA

theorem B_false (H : type_of% @OAI.HadwigerCounterexample.not_hadwiger_conjecture) :
    type_of% @ReaderB.reading_hadwiger_false := by
  intro hall
  obtain ⟨m, hm, G, hG⟩ := frozen_cex H
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  apply hG
  refine hall (Fin m) G (hadwigerNumber G) ⟨(B_minor G _).2 (frozen_mem G), fun t ht => ?_⟩
  exact le_frozen G ((B_minor G t).1 ht)

theorem C_false (H : type_of% @OAI.HadwigerCounterexample.not_hadwiger_conjecture) :
    type_of% @ReaderC.reading_hadwiger_false := by
  intro hall
  obtain ⟨m, hm, G, hG⟩ := frozen_cex H
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  apply hG
  have : ReaderC.hadwiger G = hadwigerNumber G := by
    unfold ReaderC.hadwiger hadwigerNumber
    congr 1
    ext t
    exact C_minor G t
  rw [← this]
  exact hall (Fin m) G

end TargetO.Hadwiger

#print axioms TargetO.Hadwiger.A_false
#print axioms TargetO.Hadwiger.B_false
#print axioms TargetO.Hadwiger.C_false
