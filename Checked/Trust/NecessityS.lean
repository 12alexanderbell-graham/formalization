import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegWallShearRows
import Checked.FSRev.RAssemble
import Checked.FSRev.RSeventeenOver
import Checked.FSRev.RSeventeenSlow
import Checked.FSRev.RSeventeenTube
import Checked.FSRev.REighteenOver
import Checked.FSRev.REighteenSlow
import Checked.FSRev.REighteenTube
import Checked.FSRev.RNineteenOver
import Checked.FSRev.RNineteenSlow
import Checked.FSRev.RNineteenTube

/-! Necessity witnesses (THE RESULT part 1, run 2026-11-12T1828Z): positivity of the shear is needed in the three
attached Falkner–Skan row windows β = −17/100, −18/100, −19/100 of `NegWallShearRows`. The witness is the reversed-flow
solution of each row (wall shear negative), built by the reversed-flow shooting argument (`RAssemble.core_rev`) from
three certified chains per row (`Checked/FSRev/R{Seventeen,Eighteen,Nineteen}{Over,Slow,Tube}.lean`): it meets every
other hypothesis of the window headline (the equation, the wall conditions, the edge limit and the fast-approach
class) and its wall shear is negative, outside the positive window. -/

namespace Checked.Trust.NCT

open Set Filter Topology

/-- A reversed-flow solution at a scaled coefficient K ≥ 5 with every hypothesis of a row window but positivity of the
shear, and a negative wall shear (the wall value is below `hi / √K` with `hi < 0`). -/
theorem rev_witness {K lo hi : ℝ} (hK5 : 5 ≤ K) (hlh : lo < hi) (hhi : hi < 0)
    (hO : Checked.FSAtt.ABase.ChainA K lo Checked.FSNeg.NBase.Over)
    (hS : Checked.FSAtt.ABase.ChainA K hi Checked.FSRev.RBase.SlowR)
    (hT : Checked.FSRev.RBase.TubeR K lo hi) :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / K) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧ q 0 < 0 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, _, w2⟩ :=
    Checked.FSRev.RAssemble.core_rev hK5 hlh hO hS hT
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 (by linarith)
  exact ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, w2.trans (div_neg_of_neg_of_pos hhi hs)⟩

/-- `0 < q` is needed in `fs_neg_wall_shear_17_window`. -/
theorem fs_neg_wall_shear_17_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, w⟩ := rev_witness (K := 100 / 17) (by norm_num) (by norm_num)
    (by norm_num) Checked.FSRev.RSeventeenOver.chain Checked.FSRev.RSeventeenSlow.chain
    Checked.FSRev.RSeventeenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6, a8, fun h => by norm_num at h; linarith [h.1]⟩
  have e : (-1 / (100 / 17 : ℝ)) = -17 / 100 := by norm_num
  rw [← e]; exact a3 η hη

/-- `0 < q` is needed in `fs_neg_wall_shear_18_window`. -/
theorem fs_neg_wall_shear_18_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, w⟩ := rev_witness (K := 50 / 9) (by norm_num) (by norm_num)
    (by norm_num) Checked.FSRev.REighteenOver.chain Checked.FSRev.REighteenSlow.chain
    Checked.FSRev.REighteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6, a8, fun h => by norm_num at h; linarith [h.1]⟩
  have e : (-1 / (50 / 9 : ℝ)) = -18 / 100 := by norm_num
  rw [← e]; exact a3 η hη

/-- `0 < q` is needed in `fs_neg_wall_shear_19_window`. -/
theorem fs_neg_wall_shear_19_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, w⟩ := rev_witness (K := 100 / 19) (by norm_num) (by norm_num)
    (by norm_num) Checked.FSRev.RNineteenOver.chain Checked.FSRev.RNineteenSlow.chain
    Checked.FSRev.RNineteenTube.tube
  refine ⟨f, p, q, a1, a2, fun η hη => ?_, a4, a5, a6, a8, fun h => by norm_num at h; linarith [h.1]⟩
  have e : (-1 / (100 / 19 : ℝ)) = -19 / 100 := by norm_num
  rw [← e]; exact a3 η hη

end Checked.Trust.NCT
