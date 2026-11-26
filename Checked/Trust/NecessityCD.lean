import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegDecay
import Checked.FalknerSkan.NegTenth
import Checked.FalknerSkan.NegWindow
import Checked.FSAtt.Suction
import Checked.FSAtt.SuctionSlow

/-! Hypothesis necessity for the Falkner–Skan statement on the largest wall shear with adverse pressure gradient
(`Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear`; run 2026-11-26T1228Z): hypothesis 13 (the no-suction
condition of the second solution) is NEEDED, and so is hypothesis 4 (the no-suction condition) of the bound on the
wall shear at minus one tenth (`Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt`), by the same suction solution. The witness, at minus one tenth: the attached solution of
`Checked.FalknerSkan.NegTenth.fs_neg_tenth_exists_decay` (its wall shear bounded above by
`Checked.FalknerSkan.NegWindow.fs_neg_tenth_window`) and a solution with suction at the wall, velocity tending to one
and positive second derivative, given by the slow-approach event of the certified chain `SuctionSlow` from the
scaled start of one twentieth, zero and twenty-one twentieths (`Checked.FSAtt.Suction.slow_classC`); its wall shear
exceeds the attached one. Module `NecessityCD`. -/

namespace Checked.Trust.NecessityCD
open Set Filter Topology

/-- The suction solution of the witness at minus one tenth: a solution with zero velocity at the wall, velocity
tending to one and positive second derivative, whose wall shear exceeds the attached bound. -/
theorem suction_tenth :
    ∃ g pg qg : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt g (pg η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt pg (qg η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt qg (-(g η * qg η) - (-1 / 10) * (1 - pg η ^ 2)) (Ici 0) η) ∧
      pg 0 = 0 ∧ Tendsto pg atTop (𝓝 1) ∧ (∀ η ∈ Ici (0 : ℝ), 0 < qg η) ∧
      (0.3192697599 : ℝ) < qg 0 := by
  obtain ⟨g, pg, qg, hg, hpg, hqg, -, hpg0, hqg0, hlg, hposg, -⟩ :=
    Checked.FSAtt.Suction.slow_classC (K := 10 / 1) (C := 1 / 20) (α := 21 / 20) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (Checked.FSAtt.Suction.of_chainC Checked.FSAtt.SuctionSlow.chain)
  have hK : (-1 / (10 / 1 : ℝ)) = -1 / 10 := by norm_num
  have hs : Real.sqrt (10 / 1 : ℝ) < 317 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt (10 / 1 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hgt : (0.3192697599 : ℝ) < 21 / 20 / Real.sqrt (10 / 1) := by
    rw [lt_div_iff₀ hs0]; nlinarith
  refine ⟨g, pg, qg, hg, hpg, fun η hη => ?_, hpg0, hlg, fun η hη => (hposg η hη).1, by rw [hqg0]; exact hgt⟩
  have h := hqg η hη
  rw [hK] at h; exact h

theorem fs_neg_tenth_monotone_lt_h4 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt 4 := by
  obtain ⟨g, pg, qg, hg, hpg, hqg, hpg0, hlg, hposg, hgt⟩ := suction_tenth
  exact ⟨g, pg, qg, hg, hpg, hqg, hpg0, hlg, hposg, fun hle => absurd hle (not_lt.2 hgt.le)⟩

theorem fs_neg_decay_max_shear_h13 : necessity% Checked.FalknerSkan.NegDecay.fs_neg_decay_max_shear 13 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, hp0, hlim, hpos, hdec⟩ :=
    Checked.FalknerSkan.NegTenth.fs_neg_tenth_exists_decay
  have hw := (Checked.FalknerSkan.NegWindow.fs_neg_tenth_window f p q hf hp hq hf0 hp0 hlim hpos hdec).2
  obtain ⟨g, pg, qg, hg, hpg, hqg, hpg0, hlg, hposg, hgt⟩ := suction_tenth
  exact ⟨-1 / 10, by norm_num, f, p, q, g, pg, qg, hf, hp, hq, hf0, hp0, hlim, hpos, hdec, hg, hpg, hqg, hpg0, hlg,
    hposg, fun hle => by linarith⟩

end Checked.Trust.NecessityCD
