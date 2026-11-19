import Checked.Trust.NecessityAVCertsA
import Checked.Trust.NecessityAVCertsB
import Checked.Trust.NecessityAVCertsC
import Checked.Trust.NonVacuity

/-! Hypothesis necessity for the two minimum headlines of `Checked.Data.Moresco16Min` (run
2026-11-19T0028Z). `chiSqOL_ge` bounds the open-universe chi-square of Moresco et al. from below over
the region where the matter density is at most one, the dark-energy density is nonnegative and the
squared expansion factor is nonnegative at every redshift of the table; `table5_oL_aicc_unattainable`
adds the number of data points, more than four and at most thirty-one.

All three hypotheses of `chiSqOL_ge` are REDUNDANT (each alone): the same lower bound holds where the
matter density is at least one (`regA`), where the dark-energy density is at most zero (`regB`), and,
with the two density bounds kept, with no sign condition on the squared expansion factors (`regC`; the
square root of a negative number is zero in Lean). Each region splits into a bounded box, covered by
bisection with the corner certificates of `Moresco16Min.box_boundQ` (or of `box_boundQJ`, which asks
only that each squared factor stay above minus the square of its tangent point), boxes on which one
squared factor is negative, boxes on which a row with a large ratio of value to error has a squared
factor at most zero (`neg_row`: its term alone exceeds the bound), boxes where every squared factor is
nonnegative (`chiSqOL_ge` itself), and boxes on which one row's expansion factor is so large that the
prior term or that row's term alone exceeds the bound (`far_hi`); outside the box one row forces such
a factor. The same holds for the three corresponding hypotheses of `table5_oL_aicc_unattainable`. The two bounds on the number of
data points are NEEDED: at the point of `chiSqOL_lt`, four data points (the correction term divides by
zero) or one hundred data points give a corrected criterion below the printed value plus the margin. -/

namespace Checked.Trust.NecessityAV
open Checked.Data.Moresco16 Checked.Data.Moresco16Min

theorem c_eq : (((29933 / 2000 : ℚ)) : ℝ) = 14.9665 := by norm_num

/-- The bound of `chiSqOL_ge` where the matter density is at least one (helper). -/
theorem regA (H0 m l : ℝ) (hm : 1 ≤ m) (hl : 0 ≤ l) (hy : ∀ i, 0 ≤ e2OL m l (m16Table i).1) :
    (14.9665 : ℝ) ≤ chiSqOL H0 m l := by
  rw [← c_eq]
  rcases le_total m (13 / 5) with hm1 | hm1
  · rcases le_total l (17 / 4) with hl1 | hl1
    · exact ava H0 m l hm hm1 hl hl1 hy
    · have h := hy 9
      norm_num [e2OL, m16Table] at h
      exact far_hi H0 m l 0 (1137 / 500) (by norm_num)
        (by norm_num [e2OL, m16Table]; linarith) (by norm_num [m16Table])
  · have h := hy 11
    norm_num [e2OL, m16Table] at h
    exact far_hi H0 m l 27 (381 / 125) (by norm_num)
      (by norm_num [e2OL, m16Table]; linarith) (by norm_num [m16Table])

/-- The bound of `chiSqOL_ge` where the dark-energy density is at most zero (helper). -/
theorem regB (H0 m l : ℝ) (hm : m ≤ 1) (hl : l ≤ 0) (hy : ∀ i, 0 ≤ e2OL m l (m16Table i).1) :
    (14.9665 : ℝ) ≤ chiSqOL H0 m l := by
  rw [← c_eq]
  have h := hy 29
  norm_num [e2OL, m16Table] at h
  rcases le_total (-3 / 2) m with hm0 | hm0
  · rcases le_total (-2) l with hl0 | hl0
    · exact avb H0 m l hm0 hm hl0 hl hy
    · exact far_hi H0 m l 18 (193 / 100) (by norm_num)
        (by norm_num [e2OL, m16Table]; linarith) (by norm_num [m16Table])
  · exact far_hi H0 m l 18 (193 / 100) (by norm_num)
      (by norm_num [e2OL, m16Table]; linarith) (by norm_num [m16Table])

/-- The bound of `chiSqOL_ge` with no sign condition on the squared factors (helper). -/
theorem regC (H0 m l : ℝ) (hm : m ≤ 1) (hl : 0 ≤ l) : (14.9665 : ℝ) ≤ chiSqOL H0 m l := by
  rw [← c_eq]
  rcases le_total (-3 / 5) m with hm0 | hm0
  · rcases le_total l (13 / 4) with hl1 | hl1
    · exact avc H0 m l hm0 hm hl hl1
    · exact neg_row H0 m l 28 (by norm_num [e2OL, m16Table]; linarith) (by norm_num [m16Table])
  · exact neg_row H0 m l 28 (by norm_num [e2OL, m16Table]; linarith) (by norm_num [m16Table])

/-! ### The three hypotheses of `chiSqOL_ge` are redundant -/

theorem chiSqOL_ge_r1 : dropped% Checked.Data.Moresco16Min.chiSqOL_ge 1 := by
  intro H0 m l hl hy
  rcases le_total m 1 with hm | hm
  · exact chiSqOL_ge H0 m l hm hl hy
  · exact regA H0 m l hm hl hy

theorem chiSqOL_ge_r2 : dropped% Checked.Data.Moresco16Min.chiSqOL_ge 2 := by
  intro H0 m l hm hy
  rcases le_total 0 l with hl | hl
  · exact chiSqOL_ge H0 m l hm hl hy
  · exact regB H0 m l hm hl hy

theorem chiSqOL_ge_r3 : dropped% Checked.Data.Moresco16Min.chiSqOL_ge 3 := by
  intro H0 m l hm hl
  exact regC H0 m l hm hl

/-! ### The same three hypotheses of `table5_oL_aicc_unattainable` are redundant -/

theorem aicc_of (N H0 m l : ℝ) (hN : 4 < N) (hN31 : N ≤ 31) (hc : 14.9665 ≤ chiSqOL H0 m l) :
    21.41 + 0.005 < chiSqOL H0 m l + 2 * 3 + 2 * 3 * (3 + 1) / (N - 3 - 1) := by
  have hq : (24 : ℝ) / 27 ≤ 2 * 3 * (3 + 1) / (N - 3 - 1) := by
    rw [show (2 : ℝ) * 3 * (3 + 1) = 24 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  norm_num at hq hc ⊢
  linarith

theorem table5_oL_aicc_unattainable_r3 :
    dropped% Checked.Data.Moresco16Min.table5_oL_aicc_unattainable 3 := by
  intro N H0 m l hN hN31 hl hy
  exact aicc_of N H0 m l hN hN31 (chiSqOL_ge_r1 H0 m l hl hy)

theorem table5_oL_aicc_unattainable_r4 :
    dropped% Checked.Data.Moresco16Min.table5_oL_aicc_unattainable 4 := by
  intro N H0 m l hN hN31 hm hy
  exact aicc_of N H0 m l hN hN31 (chiSqOL_ge_r2 H0 m l hm hy)

theorem table5_oL_aicc_unattainable_r5 :
    dropped% Checked.Data.Moresco16Min.table5_oL_aicc_unattainable 5 := by
  intro N H0 m l hN hN31 hm hl
  exact aicc_of N H0 m l hN hN31 (regC H0 m l hm hl)

/-! ### The two bounds on the number of data points are needed -/

theorem table5_oL_aicc_unattainable_h1 :
    necessity% Checked.Data.Moresco16Min.table5_oL_aicc_unattainable 1 := by
  obtain ⟨H0, m, l, hm0, hm1, hml, -, hpos, hchi⟩ := chiSqOL_lt
  refine ⟨4, H0, m, l, by norm_num, hm1, by linarith, fun i => (hpos i).le, ?_⟩
  norm_num
  linarith

theorem table5_oL_aicc_unattainable_h2 :
    necessity% Checked.Data.Moresco16Min.table5_oL_aicc_unattainable 2 := by
  obtain ⟨H0, m, l, hm0, hm1, hml, -, hpos, hchi⟩ := chiSqOL_lt
  refine ⟨100, H0, m, l, by norm_num, hm1, by linarith, fun i => (hpos i).le, ?_⟩
  norm_num
  linarith

end Checked.Trust.NecessityAV
