import Checked.Data.Moresco16Min

/-! The far-field bound for the chi-square of `Checked.Data.Moresco16` (helper lemma of
`Checked.Trust.NecessityAV`, run 2026-11-19T0028Z): when the expansion factor at one row of the table is
large enough, either the prior term on the Hubble constant or that row's term alone exceeds the bound of
`Checked.Data.Moresco16Min.chiSqOL_ge`. -/

namespace Checked.Trust.NecessityAV
open Checked.Data.Moresco16

/-- If `E²` at row `i` is at least `q²` and `q` is large enough against the row's value and error, the
chi-square is at least the bound of `chiSqOL_ge` (helper). -/
theorem far_hi (H0 m l : ℝ) (i : Fin 30) (q : ℝ) (hq : 0 ≤ q)
    (he : q ^ 2 ≤ e2OL m l (m16Table i).1)
    (hc : (m16Table i).2.1 + 3.87 * (m16Table i).2.2 ≤ 63.712 * q) :
    (((29933 / 2000 : ℚ)) : ℝ) ≤ chiSqOL H0 m l := by
  have hσ : 0 < (m16Table i).2.2 := by fin_cases i <;> norm_num [m16Table]
  set f : Fin 30 → ℝ := fun j =>
    (H0 * Real.sqrt (e2OL m l (m16Table j).1) - (m16Table j).2.1) ^ 2 / (m16Table j).2.2 ^ 2 with hf
  have hS : f i ≤ ∑ j, f j :=
    Finset.single_le_sum (fun j _ => by rw [hf]; positivity) (Finset.mem_univ i)
  have hS0 : 0 ≤ ∑ j, f j := Finset.sum_nonneg (fun j _ => by rw [hf]; positivity)
  have hchi : chiSqOL H0 m l = (∑ j, f j) + (H0 - 73) ^ 2 / 2.4 ^ 2 := rfl
  rw [hchi]
  push_cast
  have hP0 : 0 ≤ (H0 - 73) ^ 2 / 2.4 ^ 2 := by positivity
  rcases le_or_gt H0 63.712 with hH | hH
  · have : (29933 / 2000 : ℝ) ≤ (H0 - 73) ^ 2 / 2.4 ^ 2 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  · have hsq : q ≤ Real.sqrt (e2OL m l (m16Table i).1) :=
      le_trans (le_abs_self q) (Real.abs_le_sqrt he)
    have hx : 3.87 * (m16Table i).2.2 ≤ H0 * Real.sqrt (e2OL m l (m16Table i).1) - (m16Table i).2.1 := by
      nlinarith
    have hfi : (29933 / 2000 : ℝ) ≤ f i := by
      rw [hf]; dsimp only
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith

end Checked.Trust.NecessityAV
