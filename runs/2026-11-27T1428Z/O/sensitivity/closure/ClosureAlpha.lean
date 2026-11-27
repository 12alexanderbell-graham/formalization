import Mathlib
import Readings.sensitivity
import OAI.Combinatorics.Sensitivity.Separation

/-! # Target O, family O49: the abstract's fixed-exponent claim (run 2026-11-27T1428Z).
"For some fixed α > 2, our examples have unbounded block sensitivity and satisfy bs(f) ≥ s(f)^α" has no comparator
challenge: the frozen statement is only the ratio bound. OpenAI's scope document says the formalization also gives
it, and the solution states it as `OAI.Paper320.fixed_power_separation` (`Sensitivity/Separation.lean`), with block
sensitivity at the all-zero input. This module imports the solution (not the challenge, whose definitions share
the names; the replay's declaration comparison has shown them identical) and closes every reader's reading of the
abstract's sentence from that theorem. Its statement was read here, not frozen by a comparator. -/

namespace TargetO.SensAlpha

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



theorem bsAt_le_bs {I : Type} [Fintype I] (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f := by
  unfold blockSensitivity; exact Finset.le_sup (Finset.mem_univ x)

/-- The solution's family, shifted so that every index is at least one. -/
theorem shifted (H : type_of% @fixed_power_separation) :
    ∃ α : ℝ, 2 < α ∧ ∃ (n : ℕ → ℕ) (F : ∀ k : ℕ, (Fin (n k) → Bool) → Bool),
      (∀ k, 0 < n k ∧ (∃ x y, F k x ≠ F k y) ∧ 0 < sensitivity (F k) ∧
        (sensitivity (F k) : ℝ) ^ α ≤ blockSensitivity (F k)) ∧
      ∀ M : ℕ, ∃ k, M < blockSensitivity (F k) := by
  obtain ⟨α, hα, n, F, hall, hlim⟩ := H
  refine ⟨α, hα, fun k => n (k + 1), fun k => F (k + 1), fun k => ?_, fun M => ?_⟩
  · obtain ⟨hn, -, hnc, hp⟩ := hall (k + 1) (by omega)
    refine ⟨hn, hnc, sensitivity_pos_of_nonconstant _ hnc, hp.trans ?_⟩
    exact_mod_cast bsAt_le_bs (F (k + 1)) (fun _ => false)
  · obtain ⟨m, hm, hm1⟩ := ((hlim.eventually (Filter.eventually_gt_atTop (M : ℝ))).and
      (Filter.eventually_ge_atTop 1)).exists
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    refine ⟨k, ?_⟩
    have : blockSensitivityAt (F (k + 1)) (fun _ => false) ≤ blockSensitivity (F (k + 1)) := bsAt_le_bs _ _
    have : (M : ℝ) < blockSensitivity (F (k + 1)) := lt_of_lt_of_le hm (by exact_mod_cast this)
    exact_mod_cast this

theorem A_alpha (H : type_of% @fixed_power_separation) : type_of% @ReaderA.reading_abstract := by
  obtain ⟨α, hα, n, F, hall, hunb⟩ := shifted H
  refine ⟨α, hα, fun M => ?_⟩
  obtain ⟨k, hk⟩ := hunb M
  obtain ⟨hn, hnc, hs, hp⟩ := hall k
  refine ⟨n k, hn, F k, hnc, by rw [A_sens]; exact hs, lt_of_lt_of_le hk (A_bs _), ?_⟩
  rw [A_sens]; exact hp.trans (by exact_mod_cast A_bs _)

theorem B_alpha (H : type_of% @fixed_power_separation) : type_of% @ReaderB.reading_abstract_alpha := by
  obtain ⟨α, hα, n, F, hall, hunb⟩ := shifted H
  refine ⟨α, hα, n, F, fun k => (hall k).2.1, fun M => ?_, fun k => ?_⟩
  · obtain ⟨k, hk⟩ := hunb M
    exact ⟨k, (le_of_lt hk).trans (B_bs _)⟩
  · obtain ⟨-, -, hs, hp⟩ := hall k
    refine ⟨by rw [B_sens]; exact hs, ?_⟩
    rw [B_sens]; exact hp.trans (by exact_mod_cast B_bs _)

theorem C_alpha (H : type_of% @fixed_power_separation) : type_of% @ReaderC.reading_abstract_alpha := by
  obtain ⟨α, hα, n, F, hall, hunb⟩ := shifted H
  refine ⟨α, hα, n, F, fun k => (hall k).2.1, fun M => ?_, fun k => ?_⟩
  · obtain ⟨k, hk⟩ := hunb M
    exact ⟨k, (le_of_lt hk).trans (C_bs _)⟩
  · obtain ⟨-, -, -, hp⟩ := hall k
    rw [C_sens]; exact hp.trans (by exact_mod_cast C_bs _)

/-- The closures applied to the solution's theorem itself (axioms printed below). -/
theorem A_alpha' : type_of% @ReaderA.reading_abstract := A_alpha fixed_power_separation
theorem B_alpha' : type_of% @ReaderB.reading_abstract_alpha := B_alpha fixed_power_separation
theorem C_alpha' : type_of% @ReaderC.reading_abstract_alpha := C_alpha fixed_power_separation

end TargetO.SensAlpha

#print axioms TargetO.SensAlpha.A_alpha
#print axioms TargetO.SensAlpha.B_alpha
#print axioms TargetO.SensAlpha.C_alpha
#print axioms TargetO.SensAlpha.A_alpha'
#print axioms TargetO.SensAlpha.B_alpha'
#print axioms TargetO.SensAlpha.C_alpha'
