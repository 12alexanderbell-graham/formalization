import Mathlib
import Readings.sensitivity
import ComparatorChallenges.SensitivitySeparation

/-! # Target O, family O49 (sensitivity vs block sensitivity): closures (run 2026-11-27T1428Z).
Frozen statement `quantitative_separation` (the "More precisely" sentence), taken with `type_of%`, never retyped.
Every reader's sensitivity is proved equal to the frozen one and every reader's block sensitivity at least the
frozen one (a frozen optimal block family is a reader's block family), so the frozen statement implies each
reader's "More precisely" and each reader's first sentence of Theorem 1.1. -/

namespace TargetO.Sens

open OAI.Paper320
open scoped Classical

variable {n : ℕ}

/-- A family of `m` disjoint nonempty blocks of `Fin n` has `m ≤ n`. -/
theorem blocks_le {m : ℕ} (B : Fin m → Finset (Fin n)) (hne : ∀ j, (B j).Nonempty)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j)) : m ≤ n := by
  choose g hg using hne
  have : Function.Injective g := by
    intro i j h
    by_contra hij
    exact Finset.disjoint_left.1 (hd i j hij) (hg i) (h ▸ hg j)
  simpa using Fintype.card_le_of_injective g this

/-- The frozen block sensitivity at `x` is attained by a block family meeting the frozen condition
(generic index type, as the frozen definitions are, so the classical instances agree). -/
theorem frozen_bsAt_attained {I : Type} [Fintype I] (f : (I → Bool) → Bool) (x : I → Bool) :
    ∃ P : Finset (Finset I), (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ P, B.Nonempty ∧ f (OAI.Paper320.flip x B) ≠ f x) ∧ P.card = blockSensitivityAt f x := by
  unfold blockSensitivityAt
  obtain ⟨P, -, hP⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Finset (Finset I)))
    Finset.univ_nonempty (fun blocks : Finset (Finset I) =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (OAI.Paper320.flip x B) ≠ f x) then blocks.card else 0)
  rw [hP]
  by_cases h : (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧ (∀ B ∈ P, B.Nonempty ∧ f (OAI.Paper320.flip x B) ≠ f x)
  · exact ⟨P, h.1, h.2, by rw [if_pos h]⟩
  · exact ⟨∅, by simp, by simp, by rw [if_neg h]; rfl⟩

theorem frozen_bs_attained {I : Type} [Fintype I] (f : (I → Bool) → Bool) :
    ∃ x, blockSensitivity f = blockSensitivityAt f x := by
  unfold blockSensitivity
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (I → Bool))
    ⟨fun _ => false, Finset.mem_univ _⟩ (blockSensitivityAt f)
  exact ⟨x, hx⟩

theorem frozen_bs_attained' {I : Type} [Fintype I] (f : (I → Bool) → Bool) :
    ∃ x P, (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ P, Finset.Nonempty B ∧ f (OAI.Paper320.flip x B) ≠ f x) ∧ Finset.card P = blockSensitivity f := by
  obtain ⟨x, hx⟩ := frozen_bs_attained f
  obtain ⟨P, h1, h2, h3⟩ := frozen_bsAt_attained f x
  exact ⟨x, P, h1, h2, h3.trans hx.symm⟩

/-- A `Finset.sup` over `univ` does not depend on the `Fintype` instance. -/
theorem sup_univ_congr {α : Type} (i1 i2 : Fintype α) (g h : α → ℕ) (e : ∀ x, g x = h x) :
    (@Finset.univ α i1).sup g = (@Finset.univ α i2).sup h := by
  have : @Finset.univ α i1 = @Finset.univ α i2 := by ext; simp
  rw [this]; congr 1; funext x; exact e x

/-- An enumeration of a block set as a `Fin card`-indexed family. -/
theorem enum_family (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) (P : Finset (Finset (Fin n)))
    (h1 : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) (h2 : ∀ B ∈ P, B.Nonempty ∧ f (OAI.Paper320.flip x B) ≠ f x) :
    ∃ B : Fin P.card → Finset (Fin n), (∀ j, (B j).Nonempty) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      ∀ j, f (OAI.Paper320.flip x (B j)) ≠ f x := by
  refine ⟨fun j => (P.equivFin.symm j).1, fun j => (h2 _ (P.equivFin.symm j).2).1, fun i j hij => ?_,
    fun j => (h2 _ (P.equivFin.symm j).2).2⟩
  apply h1 _ (P.equivFin.symm i).2 _ (P.equivFin.symm j).2
  intro h
  exact hij (P.equivFin.symm.injective (Subtype.ext h))

/-! Reader A. -/

theorem A_flip (x : Fin n → Bool) (B : Finset (Fin n)) : ReaderA.flipSet x B = OAI.Paper320.flip x B := by
  funext i; simp [ReaderA.flipSet, OAI.Paper320.flip]

theorem A_sens (f : (Fin n → Bool) → Bool) : ReaderA.sens f = sensitivity f := by
  unfold ReaderA.sens sensitivity
  apply sup_univ_congr
  intro x
  unfold ReaderA.sensAt sensitivityAt
  congr 1; ext a; simp [A_flip]

theorem A_bs (f : (Fin n → Bool) → Bool) : blockSensitivity f ≤ ReaderA.bs f := by
  classical
  obtain ⟨x, P, h1, h2, h3⟩ := frozen_bs_attained' f
  rw [← h3]
  refine le_trans ?_ (Finset.le_sup (f := ReaderA.bsAt f) (Finset.mem_univ x))
  unfold ReaderA.bsAt
  refine Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩)
  · intro B hB; rw [A_flip]; exact h2 B hB
  · intro A hA B hB hAB; exact h1 A hA B hB hAB

theorem A_precise (H : type_of% @quantitative_separation) : type_of% @ReaderA.reading_thm_1_1_precise := by
  intro d hd
  obtain ⟨m, f, hm, -, hnc, hr⟩ := H d hd
  have hs : 0 < sensitivity f := by
    by_contra h0
    apply hr.not_gt
    rw [show sensitivity f = 0 by omega]; simp; positivity
  refine ⟨m, hm, f, hnc, by rw [A_sens]; exact hs, ?_⟩
  rw [A_sens]
  refine le_trans hr ?_
  gcongr; exact_mod_cast A_bs f

/-- The frozen ratio bound exceeds any `C`: some `d ≥ 1` has `C < 2^d / (4 (d+2)^2)`. -/
theorem ratio_large (C : ℝ) (hC : 0 < C) : ∃ d : ℕ, 1 ≤ d ∧ C < (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) := by
  have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).comp
    (Filter.tendsto_add_atTop_nat 2)
  have hε : (0 : ℝ) < 1 / (16 * C) := by positivity
  obtain ⟨d, hd, hd1⟩ := ((h0.eventually (gt_mem_nhds hε)).and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨d, hd1, ?_⟩
  simp only [Function.comp_apply] at hd
  push_cast at hd
  have h2 : (0 : ℝ) < 2 ^ (d + 2) := by positivity
  have hq : (0 : ℝ) < 4 * ((d : ℝ) + 2) ^ 2 := by positivity
  rw [lt_div_iff₀ hq]
  rw [div_lt_div_iff₀ h2 (by positivity)] at hd
  rw [pow_add] at hd
  nlinarith

/-- From a frozen witness `f` to a reader's two claims, given the reader's `s = sensitivity` and
`bs ≥ blockSensitivity`. -/
theorem transfer {s' bs' : ℕ} {f : (Fin n → Bool) → Bool} (hs' : s' = sensitivity f)
    (hb' : blockSensitivity f ≤ bs') (hnc : ∃ x y, f x ≠ f y) {r : ℝ}
    (hr : r ≤ (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2) (hr0 : 0 < r) :
    0 < s' ∧ r ≤ (bs' : ℝ) / (s' : ℝ) ^ 2 ∧ r * (s' : ℝ) ^ 2 ≤ bs' := by
  have hs : 0 < sensitivity f := by
    by_contra h0
    have : sensitivity f = 0 := by omega
    rw [this] at hr; simp at hr; linarith
  subst hs'
  have hsr : (0 : ℝ) < (sensitivity f : ℝ) ^ 2 := by positivity
  have hb : (blockSensitivity f : ℝ) ≤ bs' := by exact_mod_cast hb'
  refine ⟨hs, hr.trans (by gcongr), ?_⟩
  rw [le_div_iff₀ hsr] at hr; linarith

theorem first_of (H : type_of% @quantitative_separation) {s' bs' : ∀ {m : ℕ}, ((Fin m → Bool) → Bool) → ℕ}
    (hs' : ∀ {m} (f : (Fin m → Bool) → Bool), s' f = sensitivity f)
    (hb' : ∀ {m} (f : (Fin m → Bool) → Bool), blockSensitivity f ≤ bs' f) (C : ℝ) (hC : 0 < C) :
    ∃ m : ℕ, 0 < m ∧ ∃ f : (Fin m → Bool) → Bool, (∃ x y, f x ≠ f y) ∧ C * (s' f : ℝ) ^ 2 < bs' f := by
  obtain ⟨d, hd, hCd⟩ := ratio_large C hC
  obtain ⟨m, f, hm, -, hnc, hr⟩ := H d hd
  obtain ⟨hs, -, h⟩ := transfer (hs' f) (hb' f) hnc hr (by positivity)
  refine ⟨m, hm, f, hnc, lt_of_lt_of_le ?_ h⟩
  have hs0 : (0 : ℝ) < s' f := by exact_mod_cast hs
  have : (0 : ℝ) < (s' f : ℝ) ^ 2 := by positivity
  nlinarith

theorem precise_of (H : type_of% @quantitative_separation) {s' bs' : ∀ {m : ℕ}, ((Fin m → Bool) → Bool) → ℕ}
    (hs' : ∀ {m} (f : (Fin m → Bool) → Bool), s' f = sensitivity f)
    (hb' : ∀ {m} (f : (Fin m → Bool) → Bool), blockSensitivity f ≤ bs' f) (d : ℕ) (hd : 1 ≤ d) :
    ∃ m : ℕ, 0 < m ∧ ∃ f : (Fin m → Bool) → Bool, (∃ x y, f x ≠ f y) ∧ 0 < s' f ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤ (bs' f : ℝ) / (s' f : ℝ) ^ 2 := by
  obtain ⟨m, f, hm, -, hnc, hr⟩ := H d hd
  obtain ⟨hs, h, -⟩ := transfer (hs' f) (hb' f) hnc hr (by positivity)
  exact ⟨m, hm, f, hnc, hs, h⟩

theorem A_first (H : type_of% @quantitative_separation) : type_of% @ReaderA.reading_thm_1_1 := by
  intro C hC
  obtain ⟨m, hm, f, hnc, h⟩ := first_of H (s' := ReaderA.sens) (bs' := ReaderA.bs) A_sens A_bs C hC
  exact ⟨m, hm, f, hnc, h⟩

theorem A_precise' (H : type_of% @quantitative_separation) : type_of% @ReaderA.reading_thm_1_1_precise := by
  intro d hd
  obtain ⟨m, hm, f, hnc, hs, h⟩ := precise_of H (s' := ReaderA.sens) (bs' := ReaderA.bs) A_sens A_bs d hd
  exact ⟨m, hm, f, hnc, hs, h⟩

/-! Reader B. -/

theorem B_flip (x : Fin n → Bool) (B : Finset (Fin n)) : ReaderB.flipSet x B = OAI.Paper320.flip x B := by
  funext i; simp [ReaderB.flipSet, OAI.Paper320.flip]

theorem B_sens (f : (Fin n → Bool) → Bool) : ReaderB.s f = sensitivity f := by
  unfold ReaderB.s sensitivity
  apply sup_univ_congr
  intro x
  unfold ReaderB.sens sensitivityAt
  congr 1; ext a; simp [B_flip]

theorem B_bs (f : (Fin n → Bool) → Bool) : blockSensitivity f ≤ ReaderB.bs f := by
  obtain ⟨x, P, h1, h2, h3⟩ := frozen_bs_attained' f
  rw [← h3]
  refine le_trans ?_ (Finset.le_sup (f := ReaderB.bsAt f) (Finset.mem_univ x))
  obtain ⟨B, hne, hd, hfl⟩ := enum_family f x P h1 h2
  unfold ReaderB.bsAt
  exact Nat.le_findGreatest (blocks_le B hne hd) ⟨B, hne, hd, fun j => by rw [B_flip]; exact hfl j⟩

theorem B_first (H : type_of% @quantitative_separation) : type_of% @ReaderB.reading_thm_1_1_first := by
  intro C hC
  obtain ⟨m, hm, f, hnc, h⟩ := first_of H (s' := ReaderB.s) (bs' := ReaderB.bs) B_sens B_bs C hC
  exact ⟨m, hm, f, hnc, h⟩

theorem B_precise (H : type_of% @quantitative_separation) : type_of% @ReaderB.reading_thm_1_1_precise := by
  intro d hd
  obtain ⟨m, hm, f, hnc, hs, h⟩ := precise_of H (s' := ReaderB.s) (bs' := ReaderB.bs) B_sens B_bs d hd
  exact ⟨m, hm, f, hnc, hs, h⟩

/-! Reader C. -/

theorem C_flip (x : Fin n → Bool) (B : Finset (Fin n)) : ReaderC.flipSet x B = OAI.Paper320.flip x B := by
  funext i; simp [ReaderC.flipSet, OAI.Paper320.flip]

theorem C_sens (f : (Fin n → Bool) → Bool) : ReaderC.sensFn f = sensitivity f := by
  unfold ReaderC.sensFn sensitivity
  apply sup_univ_congr
  intro x
  unfold ReaderC.sens sensitivityAt
  congr 1; ext a; simp [C_flip]

theorem C_bs (f : (Fin n → Bool) → Bool) : blockSensitivity f ≤ ReaderC.bsFn f := by
  obtain ⟨x, P, h1, h2, h3⟩ := frozen_bs_attained' f
  rw [← h3]
  refine le_trans ?_ (Finset.le_sup (f := ReaderC.bsAt f) (Finset.mem_univ x))
  obtain ⟨B, hne, hd, hfl⟩ := enum_family f x P h1 h2
  unfold ReaderC.bsAt
  refine le_csSup ⟨n, ?_⟩ ⟨B, hne, hd, fun j => by rw [C_flip]; exact hfl j⟩
  rintro m ⟨B', hne', hd', -⟩
  exact blocks_le B' hne' hd'

theorem C_first (H : type_of% @quantitative_separation) : type_of% @ReaderC.reading_theorem_1_1_first := by
  intro C hC
  obtain ⟨m, hm, f, hnc, h⟩ := first_of H (s' := ReaderC.sensFn) (bs' := ReaderC.bsFn) C_sens C_bs C hC
  exact ⟨m, hm, f, hnc, h⟩

theorem C_precise (H : type_of% @quantitative_separation) : type_of% @ReaderC.reading_theorem_1_1_more_precisely := by
  intro d hd
  obtain ⟨m, hm, f, hnc, hs, h⟩ := precise_of H (s' := ReaderC.sensFn) (bs' := ReaderC.bsFn) C_sens C_bs d hd
  exact ⟨m, hm, f, hnc, hs, h⟩

end TargetO.Sens

#print axioms TargetO.Sens.A_first
#print axioms TargetO.Sens.A_precise'
#print axioms TargetO.Sens.B_first
#print axioms TargetO.Sens.B_precise
#print axioms TargetO.Sens.C_first
#print axioms TargetO.Sens.C_precise
