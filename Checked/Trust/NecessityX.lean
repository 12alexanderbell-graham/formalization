import Checked.Trust.NecessityQ
import Checked.Trust.NecessityR
import Checked.FalknerSkan.NegWallShearRowsTop
import Checked.FalknerSkan.NegReversedWallShearRows

/-! Hypothesis necessity for the attached Falkner–Skan window headlines at the first four rows of the decelerating segment of a table read blind (run 2026-11-13T1640Z), by the profiles and the edge-limit lemma that serve the sibling rows: the Falkner–Skan equation and the relation between the stream function and the velocity are needed (explicit elementary profiles valid for every pressure-gradient coefficient), positivity of the shear is needed (the reversed-flow solution of the same row, a Checked existence headline, meets every other hypothesis and has negative wall shear), and the edge limit of the velocity is redundant (it follows from the other hypotheses for a decelerating stream). -/

namespace Checked.Trust.NCX

open Set Filter Topology Checked.Trust.NCQ Checked.Trust.NCS

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_13_window`. -/
theorem fs_neg_wall_shear_13_window_h3 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_13_window`. -/
theorem fs_neg_wall_shear_13_window_h1 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_window 1 :=
  ⟨F1 (-13 / 100), P1 (-13 / 100), Q1 (-13 / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- The edge limit `p → 1` is redundant in `fs_neg_wall_shear_13_window`. -/
theorem fs_neg_wall_shear_13_window_r6 : dropped% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_14_window`. -/
theorem fs_neg_wall_shear_14_window_h3 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_14_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_14_window`. -/
theorem fs_neg_wall_shear_14_window_h1 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_14_window 1 :=
  ⟨F1 (-14 / 100), P1 (-14 / 100), Q1 (-14 / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- The edge limit `p → 1` is redundant in `fs_neg_wall_shear_14_window`. -/
theorem fs_neg_wall_shear_14_window_r6 : dropped% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_14_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_14_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_15_window`. -/
theorem fs_neg_wall_shear_15_window_h3 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_15_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_15_window`. -/
theorem fs_neg_wall_shear_15_window_h1 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_15_window 1 :=
  ⟨F1 (-15 / 100), P1 (-15 / 100), Q1 (-15 / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- The edge limit `p → 1` is redundant in `fs_neg_wall_shear_15_window`. -/
theorem fs_neg_wall_shear_15_window_r6 : dropped% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_15_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_15_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

/-- The Falkner–Skan equation is needed in `fs_neg_wall_shear_16_window`. -/
theorem fs_neg_wall_shear_16_window_h3 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_16_window 3 :=
  ⟨F, P, Q, hf_w, hp_w, F_zero, P_zero, P_lim, Q_pos, P_decay, notWin _ _ (by norm_num)⟩

/-- `f' = p` is needed in `fs_neg_wall_shear_16_window`. -/
theorem fs_neg_wall_shear_16_window_h1 : necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_16_window 1 :=
  ⟨F1 (-16 / 100), P1 (-16 / 100), Q1 (-16 / 100), hp1 _, hq1 _ (by norm_num), F1_zero _,
    P1_zero _, P1_lim _ (by norm_num), Q1_pos _ (by norm_num), P1_decay _ (by norm_num),
    notWin1 _ _ _ (by norm_num)⟩

/-- The edge limit `p → 1` is redundant in `fs_neg_wall_shear_16_window`. -/
theorem fs_neg_wall_shear_16_window_r6 : dropped% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_16_window 6 := by
  intro f p q hf hp hq hf0 hp0 hpos hdec
  exact Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_16_window f p q hf hp hq hf0 hp0
    (lim_one _ (by norm_num) f p q hf hp hq (fun η hη => (hpos η hη).le) hdec) hpos hdec

/-- `0 < q` is needed in `fs_neg_wall_shear_13_window`. -/
theorem fs_neg_wall_shear_13_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_13_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, _, w2⟩ :=
    Checked.FalknerSkan.NegReversedWallShearRows.fs_neg_reversed_wall_shear_13_exists
  refine ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, fun h => ?_⟩
  have h1 := h.1
  norm_num at h1 w2
  linarith

/-- `0 < q` is needed in `fs_neg_wall_shear_14_window`. -/
theorem fs_neg_wall_shear_14_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_14_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, _, w2⟩ :=
    Checked.FalknerSkan.NegReversedWallShearRows.fs_neg_reversed_wall_shear_14_exists
  refine ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, fun h => ?_⟩
  have h1 := h.1
  norm_num at h1 w2
  linarith

/-- `0 < q` is needed in `fs_neg_wall_shear_15_window`. -/
theorem fs_neg_wall_shear_15_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_15_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, _, w2⟩ :=
    Checked.FalknerSkan.NegReversedWallShearRows.fs_neg_reversed_wall_shear_15_exists
  refine ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, fun h => ?_⟩
  have h1 := h.1
  norm_num at h1 w2
  linarith

/-- `0 < q` is needed in `fs_neg_wall_shear_16_window`. -/
theorem fs_neg_wall_shear_16_window_h7 :
    necessity% Checked.FalknerSkan.NegWallShearRowsTop.fs_neg_wall_shear_16_window 7 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, _, a8, _, w2⟩ :=
    Checked.FalknerSkan.NegReversedWallShearRows.fs_neg_reversed_wall_shear_16_exists
  refine ⟨f, p, q, a1, a2, a3, a4, a5, a6, a8, fun h => ?_⟩
  have h1 := h.1
  norm_num at h1 w2
  linarith

end Checked.Trust.NCX
