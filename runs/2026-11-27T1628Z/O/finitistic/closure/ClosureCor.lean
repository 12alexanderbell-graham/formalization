import Mathlib
import Readings.finitistic
import ComparatorChallenges.FinitisticAsymmetry

/-! # Target O, family O58 (little finitistic dimension), Corollary 1.2: closures (run 2026-11-27T1628Z).

Frozen statement `OAI.LittleFinitistic.extreme_left_right_asymmetry` (challenge `FinitisticAsymmetry`, taken by
name, never retyped). Its dimensions are suprema in `WithBot ℕ∞` (`WithBot.instSupSet`: for a set bounded above,
which every set of `WithBot ℕ∞` is, the true supremum; no junk value), over `ModuleCat.{0}` modules of finite
Ext-based projective dimension, finitely generated for the little one. Its `InjectivesGenerate` quantifies over
isomorphism-closed, triangulated, coproduct-closed object properties of the standard derived category.

Links proved here:
* `= ⊤` gives, for every `n`, a module of finite projective dimension not `≤ n` (otherwise the supremum is `≤ n`);
* `= 0` gives `pd ≤ 0` for every module of finite projective dimension and, since `⊥ < 0`, some module with
  `pd = 0` exactly (reader A's "attained" form: `HasProjectiveDimensionLE N 0 ∧ ¬ HasProjectiveDimensionLT N 0`);
* reader A's `InjectivesGenerate` is the frozen one with two hypotheses swapped; reader B's concludes `P = ⊤`,
  equivalent to `∀ X, P X`.
Reader C (its own resolution-based `pdFree`, and no injective-generation sentence) is not closed. -/

namespace TargetO.FinitisticCor

open CategoryTheory OAI.LittleFinitistic

variable {R : Type} [Ring R]

theorem pd_lt_top_of (N : ModuleCat.{0} R) (h : ∃ k : ℕ, HasProjectiveDimensionLE N k) :
    projectiveDimension N < ⊤ :=
  lt_top_iff_ne_top.2 ((projectiveDimension_ne_top_iff N).2 h)

theorem finite_pd (N : ModuleCat.{0} R) (h : projectiveDimension N < ⊤) :
    ∃ n : ℕ, HasProjectiveDimensionLE N n :=
  (projectiveDimension_ne_top_iff N).1 (ne_of_lt h)

theorem coe_ne_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
  intro h
  have : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := h
  exact ENat.coe_ne_top n (WithBot.coe_injective this)

theorem little_top (h : littleFinitisticDimension R = ⊤) (n : ℕ) :
    ∃ N : ModuleCat.{0} R, Module.Finite R N ∧ (∃ k : ℕ, HasProjectiveDimensionLE N k) ∧
      ¬ HasProjectiveDimensionLE N n := by
  by_contra hcon
  push_neg at hcon
  have : littleFinitisticDimension R ≤ n := by
    unfold littleFinitisticDimension
    refine iSup_le fun M => iSup_le fun hfin => iSup_le fun hlt => ?_
    exact (projectiveDimension_le_iff M n).2 (hcon M hfin (finite_pd M hlt))
  rw [h, top_le_iff] at this
  exact coe_ne_top n this

theorem big_top (h : bigFinitisticDimension R = ⊤) (n : ℕ) :
    ∃ N : ModuleCat.{0} R, (∃ k : ℕ, HasProjectiveDimensionLE N k) ∧ ¬ HasProjectiveDimensionLE N n := by
  by_contra hcon
  push_neg at hcon
  have : bigFinitisticDimension R ≤ n := by
    unfold bigFinitisticDimension
    refine iSup_le fun M => iSup_le fun hlt => ?_
    exact (projectiveDimension_le_iff M n).2 (hcon M (finite_pd M hlt))
  rw [h, top_le_iff] at this
  exact coe_ne_top n this

theorem little_zero_le (h : littleFinitisticDimension R = 0) (N : ModuleCat.{0} R) (hfin : Module.Finite R N)
    (hpd : ∃ k : ℕ, HasProjectiveDimensionLE N k) : HasProjectiveDimensionLE N 0 := by
  rw [← projectiveDimension_le_iff, Nat.cast_zero, ← h]
  unfold littleFinitisticDimension
  exact le_iSup_of_le N (le_iSup_of_le hfin (le_iSup_of_le (pd_lt_top_of N hpd) le_rfl))

theorem big_zero_le (h : bigFinitisticDimension R = 0) (N : ModuleCat.{0} R)
    (hpd : ∃ k : ℕ, HasProjectiveDimensionLE N k) : HasProjectiveDimensionLE N 0 := by
  rw [← projectiveDimension_le_iff, Nat.cast_zero, ← h]
  unfold bigFinitisticDimension
  exact le_iSup_of_le N (le_iSup_of_le (pd_lt_top_of N hpd) le_rfl)

theorem pd_bot_of (N : ModuleCat.{0} R) (h0 : HasProjectiveDimensionLT N 0) : projectiveDimension N ≤ ⊥ := by
  have := (projectiveDimension_lt_iff (X := N) (n := 0)).2 h0
  rw [Nat.cast_zero, WithBot.lt_zero_iff_eq_bot] at this
  rw [this]

theorem zero_ne_bot : (0 : WithBot ℕ∞) ≠ ⊥ := WithBot.coe_ne_bot

theorem little_zero_attained (h : littleFinitisticDimension R = 0) :
    ∃ N : ModuleCat.{0} R, Module.Finite R N ∧ HasProjectiveDimensionLE N 0 ∧
      ¬ HasProjectiveDimensionLT N 0 := by
  by_contra hcon
  push_neg at hcon
  have : littleFinitisticDimension R ≤ ⊥ := by
    have h' := h
    unfold littleFinitisticDimension
    refine iSup_le fun M => iSup_le fun hfin => iSup_le fun hlt => ?_
    exact pd_bot_of M (hcon M hfin (little_zero_le h' M hfin (finite_pd M hlt)))
  rw [h, le_bot_iff] at this
  exact zero_ne_bot this

theorem big_zero_attained (h : bigFinitisticDimension R = 0) :
    ∃ N : ModuleCat.{0} R, HasProjectiveDimensionLE N 0 ∧ ¬ HasProjectiveDimensionLT N 0 := by
  by_contra hcon
  push_neg at hcon
  have : bigFinitisticDimension R ≤ ⊥ := by
    have h' := h
    unfold bigFinitisticDimension
    refine iSup_le fun M => iSup_le fun hlt => ?_
    exact pd_bot_of M (hcon M (big_zero_le h' M (finite_pd M hlt)))
  rw [h, le_bot_iff] at this
  exact zero_ne_bot this

theorem igA_iff (R : Type) [Ring R] : ReaderA.InjectivesGenerate R ↔ InjectivesGenerate R := by
  unfold ReaderA.InjectivesGenerate InjectivesGenerate
  exact ⟨fun h P h1 h2 h3 h4 => h P h2 h1 h3 h4, fun h P h1 h2 h3 h4 => h P h2 h1 h3 h4⟩

theorem igB_iff (R : Type) [Ring R] : ReaderB.InjectivesGenerate R ↔ InjectivesGenerate R := by
  unfold ReaderB.InjectivesGenerate InjectivesGenerate
  constructor
  · intro h P h1 h2 h3 h4 X
    have := h P h1 h2 h3 h4
    rw [this]; trivial
  · intro h P h1 h2 h3 h4
    funext X
    exact propext ⟨fun _ => trivial, fun _ => h P h1 h2 h3 h4 X⟩

/-! ## Reader A -/

theorem closure_A (frozen : type_of% @extreme_left_right_asymmetry) : type_of% @ReaderA.reading_cor_1_2 := by
  obtain ⟨L, _, _, hfd, h1, h2, h3, h4, h5, h6⟩ := frozen
  refine ⟨L, inferInstance, inferInstance, hfd, fun n => ?_, fun n => ?_, ⟨fun N hfin hpd => little_zero_le h3 N hfin hpd,
    little_zero_attained h3⟩, ⟨fun N hpd => big_zero_le h4 N hpd, big_zero_attained h4⟩,
    fun h => h5 ((igA_iff L).1 h), (igA_iff _).2 h6⟩
  · obtain ⟨N, hfin, hpd, hn⟩ := little_top h1 n
    exact ⟨N, hfin, hpd, hn⟩
  · obtain ⟨N, hpd, hn⟩ := big_top h2 n
    exact ⟨N, hpd, hn⟩

/-! ## Reader B -/

theorem closure_B (frozen : type_of% @extreme_left_right_asymmetry) : type_of% @ReaderB.readingCorollary12 := by
  obtain ⟨L, _, _, hfd, h1, h2, h3, h4, h5, h6⟩ := frozen
  refine ⟨L, inferInstance, inferInstance, hfd, fun n hle => ?_, fun n hle => ?_,
    fun N hfin hpd => little_zero_le h3 N hfin hpd, fun N hpd => big_zero_le h4 N hpd,
    fun h => h5 ((igB_iff L).1 h), (igB_iff _).2 h6⟩
  · obtain ⟨N, hfin, hpd, hn⟩ := little_top h1 n
    exact hn (hle N hfin hpd)
  · obtain ⟨N, hpd, hn⟩ := big_top h2 n
    exact hn (hle N hpd)

theorem reading_A_closed : type_of% @ReaderA.reading_cor_1_2 := closure_A extreme_left_right_asymmetry
theorem reading_B_closed : type_of% @ReaderB.readingCorollary12 := closure_B extreme_left_right_asymmetry

end TargetO.FinitisticCor

#print axioms TargetO.FinitisticCor.closure_A
#print axioms TargetO.FinitisticCor.closure_B
