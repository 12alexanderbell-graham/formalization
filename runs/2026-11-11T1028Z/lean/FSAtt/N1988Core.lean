import Work.FSAtt.AWindow

/-! Falkner–Skan at β = −1988/10000 (scaled coefficient K = 2500/497): the window and the existence statement of
`Work/FalknerSkan/Neg1988.lean`, from the two certified chains taken as hypotheses (the chains are
`Work.FSAtt.N1988Lo.chain` and `Work.FSAtt.N1988Hi.chain`). Run 2026-11-11T1028Z. -/

namespace Work.FSAtt.N1988Core

open Set Filter Topology Checked.FSNeg.NBase Checked.FSSep.SBase Work.FSAtt.ABase

theorem hK5 : (5 : ℝ) ≤ 2500 / 497 := by norm_num

theorem hK : (-1 / (2500 / 497 : ℝ)) = -1988 / 10000 := by norm_num

theorem sqrtK_pos : 0 < Real.sqrt (2500 / 497 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem lo_bound : (0.0052181 : ℝ) < 11703189 / 1000000000 / Real.sqrt (2500 / 497) := by
  rw [lt_div_iff₀ sqrtK_pos]
  have h : Real.sqrt (2500 / 497 : ℝ) < 11703189 / 1000000000 / 0.0052181 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h2 : (0.0052181 : ℝ) * Real.sqrt (2500 / 497) < 0.0052181 * (11703189 / 1000000000 / 0.0052181) :=
    mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : (0.0052181 : ℝ) * (11703189 / 1000000000 / 0.0052181) = 11703189 / 1000000000 := by norm_num
  linarith

theorem hi_bound : 117034 / 10000000 / Real.sqrt (2500 / 497) < (0.0052182 : ℝ) := by
  rw [div_lt_iff₀ sqrtK_pos]
  have h : 117034 / 10000000 / 0.0052182 < Real.sqrt (2500 / 497 : ℝ) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h2 : (0.0052182 : ℝ) * (117034 / 10000000 / 0.0052182) < 0.0052182 * Real.sqrt (2500 / 497) :=
    mul_lt_mul_of_pos_left h (by norm_num)
  have h3 : (0.0052182 : ℝ) * (117034 / 10000000 / 0.0052182) = 117034 / 10000000 := by norm_num
  linarith

theorem window_core (hS : ChainA (2500 / 497) (11703189 / 1000000000) SlowA)
    (hO : ChainA (2500 / 497) (117034 / 10000000) Over) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) :
    0.0052181 < q 0 ∧ q 0 < 0.0052182 := by
  have hq' : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q
      (-(f η * q η) - (-1 / (2500 / 497 : ℝ)) * (1 - p η ^ 2)) (Ici 0) η := by
    intro η hη; rw [hK]; exact hq η hη
  have W := Work.FSAtt.AWindow.window_of_chains hK5 (by norm_num) (by norm_num) (by norm_num) hS hO
    f p q hf hp hq' hf0 hp0 hlim hpos hdec
  exact ⟨lo_bound.trans W.1, W.2.trans hi_bound⟩

theorem exists_core (hS : ChainA (2500 / 497) (11703189 / 1000000000) SlowA)
    (hO : ChainA (2500 / 497) (117034 / 10000000) Over) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1988 / 10000) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, -, -⟩ :=
    Work.FSAtt.AWindow.core_window hK5 (by norm_num) (by norm_num) (by norm_num) hS hO
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6, a7, a8⟩
  rw [← hK]; exact a3 η hη

end Work.FSAtt.N1988Core
