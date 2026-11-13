import Checked.FSAtt.AWindow

/-! Falkner–Skan at the second row of the decelerating segment of the attached table read blind: the wall-shear window and the existence of a fast-approach solution from the two certified chains taken as hypotheses, with rational bounds of the square root of the scaled coefficient. Module `RFourteenCore`, promoted from `Work/FSAtt/RFourteenCore.lean`. -/

namespace Checked.FSAtt.RFourteenCore

open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Checked.FSAtt.ABase

theorem hK5 : (5 : ℝ) ≤ 100 / 14 := by norm_num

theorem hK : (-1 / (100 / 14 : ℝ)) = -14 / 100 := by norm_num

theorem sqrtK_pos : 0 < Real.sqrt (100 / 14 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem lo_bound : (0.2397359553 : ℝ) < 6407212914611 / 10000000000000 / Real.sqrt (100 / 14) := by
  rw [lt_div_iff₀ sqrtK_pos]
  have h : Real.sqrt (100 / 14 : ℝ) < 6407212914611 / 10000000000000 / 0.2397359553 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h2 : (0.2397359553 : ℝ) * Real.sqrt (100 / 14) < 0.2397359553 * (6407212914611 / 10000000000000 / 0.2397359553) :=
    mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : (0.2397359553 : ℝ) * (6407212914611 / 10000000000000 / 0.2397359553) = 6407212914611 / 10000000000000 := by norm_num
  linarith

theorem hi_bound : 1601803228987 / 2500000000000 / Real.sqrt (100 / 14) < (0.2397359554 : ℝ) := by
  rw [div_lt_iff₀ sqrtK_pos]
  have h : 1601803228987 / 2500000000000 / 0.2397359554 < Real.sqrt (100 / 14 : ℝ) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : (0.2397359554 : ℝ) * (1601803228987 / 2500000000000 / 0.2397359554) < 0.2397359554 * Real.sqrt (100 / 14) :=
    mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : (0.2397359554 : ℝ) * (1601803228987 / 2500000000000 / 0.2397359554) = 1601803228987 / 2500000000000 := by norm_num
  linarith

theorem window_core (hS : ChainA (100 / 14) (6407212914611 / 10000000000000) SlowA)
    (hO : ChainA (100 / 14) (1601803228987 / 2500000000000) Over) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.2397359553 < q 0 ∧ q 0 < 0.2397359554 := by
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(f η * q η) - (-1 / (100 / 14 : ℝ)) * (1 - p η ^ 2)) (Ici 0) η := by
    intro η hη; rw [hK]; exact hq η hη
  have W := Checked.FSAtt.AWindow.window_of_chains hK5 (by norm_num) (by norm_num) (by norm_num) hS hO
    f p q hf hp hq' hf0 hp0 hlim hpos hdec
  exact ⟨lo_bound.trans W.1, W.2.trans hi_bound⟩

theorem exists_core (hS : ChainA (100 / 14) (6407212914611 / 10000000000000) SlowA)
    (hO : ChainA (100 / 14) (1601803228987 / 2500000000000) Over) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-14 / 100) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ :=
    Checked.FSAtt.AWindow.core_window hK5 (by norm_num) (by norm_num) (by norm_num) hS hO
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6, a7, a8⟩
  rw [← hK]; exact a3 η hη

end Checked.FSAtt.RFourteenCore
