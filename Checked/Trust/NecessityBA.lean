import Checked.Trust.HzWallS
import Checked.Trust.HzWallP
import Checked.Trust.HmWallS
import Checked.Trust.HmWallP
import Checked.Trust.HzWallUS
import Checked.Trust.HzWallUP
import Checked.Trust.HmWallUS
import Checked.Trust.HmWallUP
import Checked.Trust.HzGAssemble
import Checked.Trust.HmGAssemble
import Checked.FalknerSkan.MonotoneWindow
import Checked.Hiemenz.Hiemenz
import Checked.Homann.Homann
import Checked.Trust.NonVacuity
/-! Necessity of the wall conditions (f and its derivative vanish at the wall) in the four Hiemenz and Homann shooting headlines `Checked.Hiemenz.hiemenz_over`, `Checked.Hiemenz.hiemenz_under`, `Checked.Homann.homann_over` and `Checked.Homann.homann_under`. At the upper wall shear of a bracket, a wall value of f of one tenth (`HzWallS`, `HmWallS`) or a negative wall velocity (minus one twentieth, `HzWallP`; minus one tenth, `HmWallP`) gives a solution on the whole certified window whose velocity stays below one there, so it never overshoots. At the lower wall shear, a negative wall value of f (minus one hundredth, `HzWallUS`; minus one fiftieth, `HmWallUS`) or a positive wall velocity (one hundredth, `HzWallUP`; one fiftieth, `HmWallUP`) gives a solution whose shear stays positive on the whole window, so it never undershoots. Each solution is the clamped flow on the window (Picard–Lindelöf, `ncba_local_sol`, `ncba_local_solHm`), equal to the unclamped field because the certified cells keep every clamp inactive. The wall velocity is also needed in the monotone window headlines `Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window` and `homann_monotone_window`: with a wall velocity of one tenth each boundary-value problem has a monotone solution (`HzGAssemble.exists_bvpG`, `HmGAssemble.exists_bvpG`, the suction stacks ported to a free wall velocity) whose wall shear lies below the window. Module `NecessityBA`. -/

namespace Checked.Trust.NCBA
open Set Checked.Hiemenz.HExBase Checked.Hiemenz.HExFlow Checked.Hiemenz.HCellWC

/-- A solution of the clamped Hiemenz field on [0, T] from any start. -/
theorem ncba_local_sol (y0 : ℝ × ℝ × ℝ) (T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y0 ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (vH t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 2 * T + 9 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof vH (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      y0 (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (T + 8)) :=
    { lipschitzOnWith := fun t ht => (lip ht).lipschitzOnWith
      continuousOn := fun x _ => (cont x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact norm_le ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Inside the clamps the clamped field is the Hiemenz field. -/
theorem ncba_solves {Y : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc (0 : ℝ) (15 / 2), HasDerivWithinAt Y (vH t (Y t)) (Icc 0 (15 / 2)) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) (15 / 2),
      BoxΦ (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t) :
    (∀ η ∈ Icc (0 : ℝ) (15 / 2), HasDerivWithinAt (fun t => (Y t).1) ((Y η).2.1) (Icc 0 (15 / 2)) η) ∧
    (∀ η ∈ Icc (0 : ℝ) (15 / 2), HasDerivWithinAt (fun t => (Y t).2.1) ((Y η).2.2) (Icc 0 (15 / 2)) η) ∧
    (∀ η ∈ Icc (0 : ℝ) (15 / 2), HasDerivWithinAt (fun t => (Y t).2.2)
      (-((Y η).1 * (Y η).2.2) - 1 + (Y η).2.1 ^ 2) (Icc 0 (15 / 2)) η) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨-, b2, -⟩ := hb t ht
    have d : HasDerivWithinAt (fun x => (Y x).1) (vH t (Y t)).1 (Icc 0 (15 / 2)) t := (hY t ht).fst
    exact d.congr_deriv (by simp only [vH]; exact cl_of_abs_le b2)
  · intro t ht
    obtain ⟨-, -, b3⟩ := hb t ht
    have d : HasDerivWithinAt (fun x => (Y x).2.1) (vH t (Y t)).2.1 (Icc 0 (15 / 2)) t :=
      (hY t ht).snd.fst
    exact d.congr_deriv (by simp only [vH]; exact cl_of_abs_le b3)
  · intro t ht
    obtain ⟨b1, b2, b3⟩ := hb t ht
    have d : HasDerivWithinAt (fun x => (Y x).2.2) (vH t (Y t)).2.2 (Icc 0 (15 / 2)) t :=
      (hY t ht).snd.snd
    exact d.congr_deriv
      (by simp only [vH]; rw [cl_of_abs_le b1, cl_of_abs_le b2, cl_of_abs_le b3])

/-- The wall value f(0) = 0 is needed: started from f(0) = 1/10 (and p(0) = 0, the upper wall shear of the
bracket) the solution keeps p below one on the whole window, so it does not overshoot. -/
theorem hiemenz_over_h5 : necessity% Checked.Hiemenz.hiemenz_over 5 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_sol (1 / 10, 0, 1.2325876569) (15 / 2) (by norm_num)
  have hP := Checked.Trust.HzWallS.chainP hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solves hY (Checked.Trust.HzWallS.boxC hY hY0)
  refine ⟨15 / 2, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hP η ⟨hη.1.le, hη.2⟩]

/-- The wall velocity p(0) = 0 is needed: started from p(0) = −1/20 (and f(0) = 0, the upper wall shear of
the bracket) the solution keeps p below one on the whole window, so it does not overshoot. -/
theorem hiemenz_over_h6 : necessity% Checked.Hiemenz.hiemenz_over 6 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_sol (0, -1 / 20, 1.2325876569) (15 / 2) (by norm_num)
  have hP := Checked.Trust.HzWallP.chainP hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solves hY (Checked.Trust.HzWallP.boxC hY hY0)
  refine ⟨15 / 2, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hP η ⟨hη.1.le, hη.2⟩]

/-- A solution of the clamped Homann field on [0, T] from any start. -/
theorem ncba_local_solHm (y0 : ℝ × ℝ × ℝ) (T : ℝ) (hT : 0 < T) : ∃ Y : ℝ → ℝ × ℝ × ℝ, Y 0 = y0 ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt Y (Checked.Homann.HmExBase.vH t (Y t)) (Icc 0 T) t := by
  set L : ℝ := 4 * T + 13 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof Checked.Homann.HmExBase.vH (tmin := 0) (tmax := T) ⟨0, le_rfl, hT.le⟩
      y0 (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (2 * T + 12)) :=
    { lipschitzOnWith := fun t ht => (Checked.Homann.HmExFlow.lip ht).lipschitzOnWith
      continuousOn := fun x _ => (Checked.Homann.HmExFlow.cont x).continuousOn
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact Checked.Homann.HmExFlow.norm_le ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, Real.coe_toNNReal _ (by positivity)]
        simp only [NNReal.coe_zero, sub_zero, sub_self]
        rw [max_eq_left hT.le] }
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Inside the clamps the clamped Homann field is the Homann field. -/
theorem ncba_solvesHm {Y : ℝ → ℝ × ℝ × ℝ}
    (hY : ∀ t ∈ Icc (0 : ℝ) 6, HasDerivWithinAt Y (Checked.Homann.HmExBase.vH t (Y t)) (Icc 0 6) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) 6,
      Checked.Homann.HmCellWC.BoxΦ (fun t => (Y t).1) (fun t => (Y t).2.1) (fun t => (Y t).2.2) t) :
    (∀ η ∈ Icc (0 : ℝ) 6, HasDerivWithinAt (fun t => (Y t).1) ((Y η).2.1) (Icc 0 6) η) ∧
    (∀ η ∈ Icc (0 : ℝ) 6, HasDerivWithinAt (fun t => (Y t).2.1) ((Y η).2.2) (Icc 0 6) η) ∧
    (∀ η ∈ Icc (0 : ℝ) 6, HasDerivWithinAt (fun t => (Y t).2.2)
      (-(2 * (Y η).1 * (Y η).2.2) - 1 + (Y η).2.1 ^ 2) (Icc 0 6) η) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨-, b2, -⟩ := hb t ht
    have d : HasDerivWithinAt (fun x => (Y x).1) (Checked.Homann.HmExBase.vH t (Y t)).1 (Icc 0 6) t :=
      (hY t ht).fst
    exact d.congr_deriv (by
      simp only [Checked.Homann.HmExBase.vH]; exact Checked.Homann.HmExBase.cl_of_abs_le b2)
  · intro t ht
    obtain ⟨-, -, b3⟩ := hb t ht
    have d : HasDerivWithinAt (fun x => (Y x).2.1) (Checked.Homann.HmExBase.vH t (Y t)).2.1 (Icc 0 6) t :=
      (hY t ht).snd.fst
    exact d.congr_deriv (by
      simp only [Checked.Homann.HmExBase.vH]; exact Checked.Homann.HmExBase.cl_of_abs_le b3)
  · intro t ht
    obtain ⟨b1, b2, b3⟩ := hb t ht
    have d : HasDerivWithinAt (fun x => (Y x).2.2) (Checked.Homann.HmExBase.vH t (Y t)).2.2 (Icc 0 6) t :=
      (hY t ht).snd.snd
    exact d.congr_deriv (by
      simp only [Checked.Homann.HmExBase.vH]
      rw [Checked.Homann.HmExBase.cl_of_abs_le b1, Checked.Homann.HmExBase.cl_of_abs_le b2,
        Checked.Homann.HmExBase.cl_of_abs_le b3])

/-- Homann: the wall value f(0) = 0 is needed: started from f(0) = 1/10 (and p(0) = 0, the upper wall
shear of the bracket) the solution keeps p below one on the whole window, so it does not overshoot. -/
theorem homann_over_h5 : necessity% Checked.Homann.homann_over 5 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_solHm (1 / 10, 0, 1.3119376939) 6 (by norm_num)
  have hP := Checked.Trust.HmWallS.chainP hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solvesHm hY (Checked.Trust.HmWallS.boxC hY hY0)
  refine ⟨6, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hP η ⟨hη.1.le, hη.2⟩]

/-- Homann: the wall velocity p(0) = 0 is needed: started from p(0) = −1/10 (and f(0) = 0, the upper wall
shear of the bracket) the solution keeps p below one on the whole window, so it does not overshoot. -/
theorem homann_over_h6 : necessity% Checked.Homann.homann_over 6 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_solHm (0, -1 / 10, 1.3119376939) 6 (by norm_num)
  have hP := Checked.Trust.HmWallP.chainP hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solvesHm hY (Checked.Trust.HmWallP.boxC hY hY0)
  refine ⟨6, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hP η ⟨hη.1.le, hη.2⟩]

/-- The wall value f(0) = 0 is needed: started from f(0) = −1/100 (and p(0) = 0, the lower wall shear of the
bracket) the solution keeps q positive on the whole window, so it does not undershoot. -/
theorem hiemenz_under_h5 : necessity% Checked.Hiemenz.hiemenz_under 5 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_sol (-1 / 100, 0, 1.2325876568) (15 / 2) (by norm_num)
  have hQ := Checked.Trust.HzWallUS.chainQ hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solves hY (Checked.Trust.HzWallUS.boxC hY hY0)
  refine ⟨15 / 2, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hQ η ⟨hη.1.le, hη.2⟩]

/-- The wall velocity p(0) = 0 is needed: started from p(0) = 1/100 (and f(0) = 0, the lower wall shear of
the bracket) the solution keeps q positive on the whole window, so it does not undershoot. -/
theorem hiemenz_under_h6 : necessity% Checked.Hiemenz.hiemenz_under 6 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_sol (0, 1 / 100, 1.2325876568) (15 / 2) (by norm_num)
  have hQ := Checked.Trust.HzWallUP.chainQ hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solves hY (Checked.Trust.HzWallUP.boxC hY hY0)
  refine ⟨15 / 2, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hQ η ⟨hη.1.le, hη.2⟩]

/-- Homann: the wall value f(0) = 0 is needed: started from f(0) = −1/50 (and p(0) = 0, the lower wall
shear of the bracket) the solution keeps q positive on the whole window, so it does not undershoot. -/
theorem homann_under_h5 : necessity% Checked.Homann.homann_under 5 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_solHm (-1 / 50, 0, 1.3119376938) 6 (by norm_num)
  have hQ := Checked.Trust.HmWallUS.chainQ hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solvesHm hY (Checked.Trust.HmWallUS.boxC hY hY0)
  refine ⟨6, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hQ η ⟨hη.1.le, hη.2⟩]

/-- Homann: the wall velocity p(0) = 0 is needed: started from p(0) = 1/50 (and f(0) = 0, the lower wall
shear of the bracket) the solution keeps q positive on the whole window, so it does not undershoot. -/
theorem homann_under_h6 : necessity% Checked.Homann.homann_under 6 := by
  obtain ⟨Y, hY0, hY⟩ := ncba_local_solHm (0, 1 / 50, 1.3119376938) 6 (by norm_num)
  have hQ := Checked.Trust.HmWallUP.chainQ hY hY0
  obtain ⟨hf, hp, hq⟩ := ncba_solvesHm hY (Checked.Trust.HmWallUP.boxC hY hY0)
  refine ⟨6, le_rfl, fun t => (Y t).1, fun t => (Y t).2.1, fun t => (Y t).2.2, hf, hp, hq,
    by simp [hY0], by simp [hY0], ?_⟩
  rintro ⟨η, hη, h1, -⟩
  linarith [hQ η ⟨hη.1.le, hη.2⟩]

/-- The wall velocity p(0) = 0 is needed in the monotone Hiemenz window: with p(0) = 1/10 there is a
monotone solution (q > 0, p → 1) with wall shear between 1.1 and 1.2, below the window. -/
theorem hiemenz_monotone_window_h5 :
    necessity% Checked.FalknerSkan.MonotoneWindow.hiemenz_monotone_window 5 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, -, hl, -, hhi, hc⟩ := Checked.Trust.HzGAssemble.exists_bvpG
  refine ⟨f, p, q, hf, hp, hq, hf0, hl, fun η hη => (hc η hη).2.2, ?_⟩
  rintro ⟨h1, -⟩
  norm_num at hhi h1
  linarith

/-- The wall velocity p(0) = 0 is needed in the monotone Homann window: with p(0) = 1/10 there is a
monotone solution (q > 0, p → 1) with wall shear between 1.18 and 1.28, below the window. -/
theorem homann_monotone_window_h5 :
    necessity% Checked.FalknerSkan.MonotoneWindow.homann_monotone_window 5 := by
  obtain ⟨f, p, q, hf, hp, hq, hf0, -, hl, -, hhi, hc⟩ := Checked.Trust.HmGAssemble.exists_bvpG
  refine ⟨f, p, q, hf, hp, hq, hf0, hl, fun η hη => (hc η hη).2.2, ?_⟩
  rintro ⟨h1, -⟩
  norm_num at hhi h1
  linarith

end Checked.Trust.NCBA
