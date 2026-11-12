import Checked.Trust.NonVacuity
import Checked.FalknerSkan.NegWindow
import Checked.FalknerSkan.NegWallShear
import Checked.FalknerSkan.NegWallShearRows
import Checked.Records.FalknerSkan

/-! Hypothesis necessity for the Falkner–Skan window headlines with adverse pressure gradient (run 2026-11-12T1428Z), by explicit elementary profiles that meet every other hypothesis whatever the pressure-gradient coefficient: the Falkner–Skan equation is needed (a profile with a Gaussian-type approach to the edge value whose wall shear lies outside every window), and the relation between the stream function and the velocity is needed (velocity and shear from the same kind of profile, the stream function read off the equation). -/

namespace Checked.Trust.NCQ

open Set Filter Topology

noncomputable def u (η : ℝ) : ℝ := η + η ^ 2 / 4
noncomputable def F (η : ℝ) : ℝ := η - 1 + Real.exp (-u η)
noncomputable def P (η : ℝ) : ℝ := 1 - (1 + η / 2) * Real.exp (-u η)
noncomputable def Q (η : ℝ) : ℝ := ((1 + η / 2) ^ 2 - 1 / 2) * Real.exp (-u η)

theorem u_deriv (η : ℝ) : HasDerivAt (fun x => -u x) (-(1 + η / 2)) η := by
  have h := ((hasDerivAt_id η).add ((hasDerivAt_pow 2 η).div_const 4)).neg
  convert h using 1
  · ext x; simp [u]
  · simp; ring

theorem F_deriv (η : ℝ) : HasDerivAt F (P η) η := by
  have h := ((hasDerivAt_id η).sub_const 1).add (u_deriv η).exp
  convert h using 1
  · ext x; simp [F]
  · simp [P]; ring

theorem P_deriv (η : ℝ) : HasDerivAt P (Q η) η := by
  have h := (hasDerivAt_const η (1 : ℝ)).sub
    ((((hasDerivAt_id η).div_const 2).const_add 1).mul (u_deriv η).exp)
  convert h using 1
  · ext x; simp [P]
  · simp [Q]; ring

theorem Q_pos (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) : 0 < Q η := by
  simp only [mem_Ici] at hη
  unfold Q; apply mul_pos _ (Real.exp_pos _); nlinarith

theorem F_zero : F 0 = 0 := by simp [F, u]
theorem P_zero : P 0 = 0 := by simp [P, u]
theorem Q_zero : Q 0 = 1 / 2 := by simp [Q, u]; norm_num

/-- e^{−u} (1 + η/2) → 0. -/
theorem tail : Tendsto (fun η => (1 + η / 2) * Real.exp (-u η)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun η : ℝ => (1 + η / 2) * Real.exp (-η)) atTop (𝓝 0) := by
    have a := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have b := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have := b.add (a.div_const 2)
    simp only [pow_one, pow_zero, one_mul, add_zero, zero_div] at this
    refine this.congr (fun η => ?_); ring
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with η hη
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with η hη
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.2; simp only [u]; nlinarith [sq_nonneg η]

theorem P_lim : Tendsto P atTop (𝓝 1) := by
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub tail
  simp only [sub_zero] at this
  exact this.congr (fun η => by simp [P])

theorem P_decay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P η) ≤ Q η := by
  intro M
  filter_upwards [eventually_ge_atTop (2 * |M| + 2)] with η hη
  have hM := le_abs_self M
  have e := Real.exp_pos (-u η)
  have h1 : 1 - P η = (1 + η / 2) * Real.exp (-u η) := by simp [P]
  rw [h1, Q, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ e.le
  nlinarith [abs_nonneg M]

theorem hf_w : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt F (P η) (Ici 0) η :=
  fun η _ => (F_deriv η).hasDerivWithinAt
theorem hp_w : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt P (Q η) (Ici 0) η :=
  fun η _ => (P_deriv η).hasDerivWithinAt

theorem notWin (a b : ℝ) (hb : b < 1 / 2) : ¬ (a < Q 0 ∧ Q 0 < b) := by
  rw [Q_zero]; intro h; linarith [h.2]

/-- The Falkner–Skan equation is needed in `fs_neg_tenth_window`. -/
theorem fs_neg_tenth_window_h3 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_window`. -/
theorem fs_neg_wall_shear_window_h3 : necessity% Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_17_window`. -/
theorem fs_neg_wall_shear_17_window_h3 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_18_window`. -/
theorem fs_neg_wall_shear_18_window_h3 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_19_window`. -/
theorem fs_neg_wall_shear_19_window_h3 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- The Falkner–Skan equation is needed in `F13_wall_shear`. -/
theorem F13_wall_shear_h3 : necessity% Checked.Records.F13_wall_shear 3 := by
  refine ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioWall; rw [Q_zero, abs_le]; norm_num

/-! The relation between the stream function and the velocity dropped: velocity and shear from a Gaussian-type profile, the stream function read off the equation. -/

noncomputable def v (b η : ℝ) : ℝ := η + (1 - b) / 2 * η ^ 2
noncomputable def P1 (b η : ℝ) : ℝ := 1 - Real.exp (-v b η)
noncomputable def Q1 (b η : ℝ) : ℝ := (1 + (1 - b) * η) * Real.exp (-v b η)
noncomputable def R1 (b η : ℝ) : ℝ := ((1 - b) - (1 + (1 - b) * η) ^ 2) * Real.exp (-v b η)
noncomputable def F1 (b η : ℝ) : ℝ := -(R1 b η + b * (1 - P1 b η ^ 2)) / Q1 b η

theorem v_deriv (b η : ℝ) : HasDerivAt (fun x => -v b x) (-(1 + (1 - b) * η)) η := by
  have h := ((hasDerivAt_id η).add ((hasDerivAt_pow 2 η).const_mul ((1 - b) / 2))).neg
  convert h using 1
  · ext x; simp [v]
  · simp; ring

theorem P1_deriv (b η : ℝ) : HasDerivAt (P1 b) (Q1 b η) η := by
  have h := (hasDerivAt_const η (1 : ℝ)).sub (v_deriv b η).exp
  convert h using 1
  · ext x; simp [P1]
  · simp [Q1]; ring

theorem Q1_deriv (b η : ℝ) : HasDerivAt (Q1 b) (R1 b η) η := by
  have h := (((hasDerivAt_id η).const_mul (1 - b)).const_add 1).mul (v_deriv b η).exp
  convert h using 1
  · ext x; simp [Q1]
  · simp [R1]; ring

theorem Q1_pos (b : ℝ) (hb : b < 1) (η : ℝ) (hη : η ∈ Ici (0 : ℝ)) : 0 < Q1 b η := by
  simp only [mem_Ici] at hη
  unfold Q1; apply mul_pos _ (Real.exp_pos _); nlinarith

theorem hq1 (b : ℝ) (hb : b < 1) : ∀ η ∈ Ici (0 : ℝ),
    HasDerivWithinAt (Q1 b) (-(F1 b η * Q1 b η) - b * (1 - P1 b η ^ 2)) (Ici 0) η := by
  intro η hη
  have hQ := (Q1_pos b hb η hη).ne'
  refine (Q1_deriv b η).hasDerivWithinAt.congr_deriv ?_
  unfold F1; field_simp; ring

theorem F1_zero (b : ℝ) : F1 b 0 = 0 := by
  simp [F1, R1, P1, Q1, v]

theorem P1_lim (b : ℝ) (hb : b < 1) : Tendsto (P1 b) atTop (𝓝 1) := by
  have hv : Tendsto (v b) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with η hη
    have : 0 ≤ (1 - b) / 2 * η ^ 2 := mul_nonneg (by linarith) (sq_nonneg η)
    simp only [v, id]; linarith
  have h : Tendsto (fun η => Real.exp (-v b η)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hv
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simp only [sub_zero] at this
  exact this.congr (fun η => by simp [P1])

theorem P1_decay (b : ℝ) (hb : b < 1) : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - P1 b η) ≤ Q1 b η := by
  intro M
  filter_upwards [eventually_ge_atTop ((|M| + 1) / (1 - b))] with η hη
  have hM := le_abs_self M
  have h1b : 0 < 1 - b := by linarith
  have h2 : |M| + 1 ≤ (1 - b) * η := by rwa [div_le_iff₀ h1b, mul_comm] at hη
  have h1 : 1 - P1 b η = Real.exp (-v b η) := by simp [P1]
  rw [h1, Q1]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  linarith

theorem Q1_zero (b : ℝ) : Q1 b 0 = 1 := by simp [Q1, v]

theorem hp1 (b : ℝ) : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt (P1 b) (Q1 b η) (Ici 0) η :=
  fun η _ => (P1_deriv b η).hasDerivWithinAt

theorem P1_zero (b : ℝ) : P1 b 0 = 0 := by simp [P1, v]

theorem notWin1 (b x y : ℝ) (hy : y < 1) : ¬ (x < Q1 b 0 ∧ Q1 b 0 < y) := by
  rw [Q1_zero]; intro h; linarith [h.2]

/-- `f' = p` is needed in `fs_neg_tenth_window`. -/
theorem fs_neg_tenth_window_h1 : necessity% Checked.FalknerSkan.NegWindow.fs_neg_tenth_window 1 :=
  ⟨F1 (-1 / 10), P1 (-1 / 10), Q1 (-1 / 10), hp1 _, hq1 _ (by norm_num), F1_zero _, P1_zero _,
    P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num), notWin1 _ _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_window`. -/
theorem fs_neg_wall_shear_window_h1 : necessity% Checked.FalknerSkan.NegWallShear.fs_neg_wall_shear_window 1 :=
  ⟨F1 (-1988 / 10000), P1 (-1988 / 10000), Q1 (-1988 / 10000), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_17_window`. -/
theorem fs_neg_wall_shear_17_window_h1 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_17_window 1 :=
  ⟨F1 (-17 / 100), P1 (-17 / 100), Q1 (-17 / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_18_window`. -/
theorem fs_neg_wall_shear_18_window_h1 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_18_window 1 :=
  ⟨F1 (-18 / 100), P1 (-18 / 100), Q1 (-18 / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_19_window`. -/
theorem fs_neg_wall_shear_19_window_h1 :
    necessity% Checked.FalknerSkan.NegWallShearRows.fs_neg_wall_shear_19_window 1 :=
  ⟨F1 (-19 / 100), P1 (-19 / 100), Q1 (-19 / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- `f' = p` is needed in `F13_wall_shear`. -/
theorem F13_wall_shear_h1 : necessity% Checked.Records.F13_wall_shear 1 := by
  refine ⟨F1 (-1988 / 10000), P1 (-1988 / 10000), Q1 (-1988 / 10000), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num), ?_⟩
  unfold Checked.Records.RoundsTo Checked.Records.printedFazioWall; rw [Q1_zero, abs_le]; norm_num

end Checked.Trust.NCQ
