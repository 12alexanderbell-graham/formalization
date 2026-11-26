import Checked.Trust.NonVacuity
import Checked.FalknerSkan.Separation
import Checked.FalknerSkan.SeparationEqual
import Checked.Records.FalknerSkan
import Checked.FSSep.SuctionSep
import Checked.FSSep.SuctionSepOver
import Checked.FSSep.SuctionSepSlow
import Checked.FSSep.WallSep
import Checked.FSSep.WallSepOver
import Checked.FSSep.WallSepSlow
import Checked.FSSep.SSlowSol
import Checked.FSSep.SSlowFiveThree
import Checked.FSSep.BlowSep
import Checked.FSSep.BlowSepOver
import Checked.FSSep.BlowSepSlow
import Checked.FalknerSkan.SeparationPrinted

/-! Hypothesis necessity for the uniqueness of the Falkner–Skan separation value
(`Checked.FalknerSkan.SeparationEqual.fs_separation_equal`) and the record of the printed separation value
(`Checked.Records.F12_separation`; run 2026-11-26T1228Z): the zero stream function and the zero velocity
at the wall are NEEDED (hypotheses 4, 5, 13 and 14 of the first, 4 and 5 of the second). The witnesses: the separation
solution of `Checked.FalknerSkan.Separation.fs_separation_exists`, a separation solution with suction at the wall
(`Checked.FSSep.SuctionSep.core_sepS`, chains `SuctionSepOver` and `SuctionSepSlow`) and a separation solution with
the wall moving with the stream (`Checked.FSSep.WallSep.core_sepW`, chains `WallSepOver` and `WallSepSlow`): each
has zero shear at the wall, velocity tending to one, positive shear after the wall and the fast approach, and its
pressure-gradient coefficient lies below the window of the first, far from the printed value. The fast approach is
NEEDED in the record and in the bound below the printed value
(`Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed`, hypothesis 9 of each): the slow-approach
solution of `Checked.FSSep.SSlowSol.slow_sol` from the certified chain `SSlowFiveThree` has zero shear at the wall,
velocity tending to one and positive shear after the wall, at a coefficient above the printed value. The zero stream
function at the wall is NEEDED in that bound too (hypothesis 4): a separation solution with blowing at the wall
(`Checked.FSSep.BlowSep.core_sepS`, chains `BlowSepOver` and `BlowSepSlow`) has its coefficient above the printed
value. Module `NecessityCE`. -/

namespace Checked.Trust.NecessityCE
open Set Filter Topology

/-- A separation solution with suction at the wall whose pressure-gradient coefficient lies below that of
`fs_separation_exists`. -/
theorem suction_sep :
    ∃ β : ℝ, β < -(1996 / 10000) ∧ ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) ∧
      0 < f 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  obtain ⟨β, -, hβ, f, p, q, h⟩ :=
    Checked.FSSep.SuctionSep.core_sepS (lo := 5007 / 1000) (hi := 5009 / 1000) (by norm_num) (by norm_num)
      Checked.FSSep.SuctionSepOver.chain Checked.FSSep.SuctionSepSlow.chain
  exact ⟨β, by norm_num at hβ ⊢; linarith, f, p, q, h⟩

/-- A separation solution with the wall moving with the stream whose pressure-gradient coefficient lies below that
of `fs_separation_exists`. -/
theorem wall_sep :
    ∃ β : ℝ, β < -(1993 / 10000) ∧ ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ 0 < p 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  obtain ⟨β, -, hβ, f, p, q, h⟩ :=
    Checked.FSSep.WallSep.core_sepW (lo := 5014 / 1000) (hi := 5016 / 1000) (by norm_num) (by norm_num)
      Checked.FSSep.WallSepOver.chain Checked.FSSep.WallSepSlow.chain
  exact ⟨β, by norm_num at hβ ⊢; linarith, f, p, q, h⟩

theorem fs_separation_equal_h4 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 4 := by
  obtain ⟨β₁, hβ₁, f₁, p₁, q₁, a1, a2, a3, -, a5, a6, a7, a8, a9⟩ := suction_sep
  obtain ⟨β₂, hβ₂, f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  exact ⟨β₁, β₂, f₁, p₁, q₁, f₂, p₂, q₂, a1, a2, a3, a5, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    fun he => by linarith [hβ₂.1]⟩

theorem fs_separation_equal_h13 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 13 := by
  obtain ⟨β₂, hβ₂, f₂, p₂, q₂, a1, a2, a3, -, a5, a6, a7, a8, a9⟩ := suction_sep
  obtain ⟨β₁, hβ₁, f₁, p₁, q₁, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  exact ⟨β₁, β₂, f₁, p₁, q₁, f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8, b9, a1, a2, a3, a5, a6, a7, a8, a9,
    fun he => by linarith [hβ₁.1]⟩

theorem fs_separation_equal_h5 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 5 := by
  obtain ⟨β₁, hβ₁, f₁, p₁, q₁, a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := wall_sep
  obtain ⟨β₂, hβ₂, f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  exact ⟨β₁, β₂, f₁, p₁, q₁, f₂, p₂, q₂, a1, a2, a3, a4, a6, a7, a8, a9, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    fun he => by linarith [hβ₂.1]⟩

theorem fs_separation_equal_h14 : necessity% Checked.FalknerSkan.SeparationEqual.fs_separation_equal 14 := by
  obtain ⟨β₂, hβ₂, f₂, p₂, q₂, a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := wall_sep
  obtain ⟨β₁, hβ₁, f₁, p₁, q₁, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ :=
    Checked.FalknerSkan.Separation.fs_separation_exists
  exact ⟨β₁, β₂, f₁, p₁, q₁, f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8, b9, a1, a2, a3, a4, a6, a7, a8, a9,
    fun he => by linarith [hβ₁.1]⟩

theorem F12_separation_h4 : necessity% Checked.Records.F12_separation 4 := by
  obtain ⟨β, hβ, f, p, q, a1, a2, a3, -, a5, a6, a7, a8, a9⟩ := suction_sep
  refine ⟨β, f, p, q, a1, a2, a3, a5, a6, a7, a8, a9, fun h => ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioSeparation at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

theorem F12_separation_h5 : necessity% Checked.Records.F12_separation 5 := by
  obtain ⟨β, hβ, f, p, q, a1, a2, a3, a4, -, a6, a7, a8, a9⟩ := wall_sep
  refine ⟨β, f, p, q, a1, a2, a3, a4, a6, a7, a8, a9, fun h => ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioSeparation at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- A slow-approach separation solution (no fast approach) at the coefficient minus one hundred over five hundred
and three, above the printed separation value. -/
theorem slow_sep :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-(100 / 503 : ℝ)) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) := by
  have h := Checked.FSSep.SSlowSol.slow_sol (K := 503 / 100) (by norm_num)
    (Checked.FSSep.SFlow.of_chain Checked.FSSep.SSlowFiveThree.chain)
  have e : (-(1 / (503 / 100 : ℝ))) = -(100 / 503 : ℝ) := by norm_num
  rw [e] at h
  exact h

theorem F12_separation_h9 : necessity% Checked.Records.F12_separation 9 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8⟩ := slow_sep
  refine ⟨-(100 / 503), f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, fun h => ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioSeparation at h
  rw [abs_le] at h
  norm_num at h

theorem fs_separation_below_printed_h9 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 9 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8⟩ := slow_sep
  exact ⟨-(100 / 503), f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, by norm_num⟩

/-- A separation solution with blowing at the wall whose pressure-gradient coefficient lies above the printed
separation value. -/
theorem blow_sep :
    ∃ β : ℝ, -(1981 / 10000) < β ∧ ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 < 0 ∧ p 0 = 0 ∧ q 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ioi (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  obtain ⟨β, hβ, -, f, p, q, h⟩ :=
    Checked.FSSep.BlowSep.core_sepS (lo := 5049 / 1000) (hi := 5052 / 1000) (by norm_num) (by norm_num)
      (by norm_num) Checked.FSSep.BlowSepOver.chain Checked.FSSep.BlowSepSlow.chain
  exact ⟨β, by norm_num at hβ ⊢; linarith, f, p, q, h⟩

theorem fs_separation_below_printed_h4 :
    necessity% Checked.FalknerSkan.SeparationPrinted.fs_separation_below_printed 4 := by
  obtain ⟨β, hβ, f, p, q, a1, a2, a3, -, a5, a6, a7, a8, a9⟩ := blow_sep
  exact ⟨β, f, p, q, a1, a2, a3, a5, a6, a7, a8, a9, fun h => by linarith⟩

end Checked.Trust.NecessityCE
