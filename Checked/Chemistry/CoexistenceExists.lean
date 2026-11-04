import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.CoexistenceReduced

/-!
# Existence of the van der Waals coexistence state at T = 0.7 T_c (run 2026-11-04T0028Z)

Promoted from `Work/Chemistry/CoexistenceExists.lean` (imports narrowed, namespace changed).

Reduced variables as in `Checked.Chemistry.CoexistenceReduced` (`x = v/b`, `π = p/P_c`,
`g x = (28/5)/(x−1) − 27/x²`, `ψ π x = (28/5) log(x−1) + 27/x − π x`).

**Route (no root functions of the pressure).** For each pressure `π` let
`M₁(π) = max ψ π` on the liquid window `[1.1, 1.49]` and `M₂(π) = max ψ π` on the gas window
`[23, 30]`. Both are continuous in `π` (supremum of a jointly continuous function over a compact
set, `IsCompact.continuous_sSup`). For `π ∈ [0.200455, 0.200465]` every maximizer is interior
(`left_loc`, `right_loc`: `ψ π` strictly increases, then strictly decreases, across rational
points where `g` is above / below the whole window), hence a critical point: `g x = π`.
At `π = 0.200455` the gas maximum is higher (`Dgap_lo`, certificate `K_lo`), at `π = 0.200465`
the liquid maximum is higher (`Dgap_hi`, certificate `K_hi`). The intermediate value theorem
gives `π*` with equal maxima: the two maximizers are a Maxwell coexistence state.

Then `acentric_window` turns the pressure window into the acentric factor to 4 decimals
(log 10 from `1000 = 2¹⁰ (1 − 3/128)` and a 4-term series; log(5π) from `1 − 1/y ≤ log y ≤ y − 1`).
-/

namespace Checked.Chemistry.CoexistenceReduced

open Real Set Checked.Records Checked.Chemistry.CubicEOS

/-- `ψ` with the volume clamped to `x ≥ 1.1` (jointly continuous; equals `ψ` on both windows). -/
noncomputable def ψc (p x : ℝ) : ℝ := ψ p (max x (11 / 10))

lemma ψc_eq {p x : ℝ} (h : 11 / 10 ≤ x) : ψc p x = ψ p x := by
  unfold ψc; rw [max_eq_left h]

lemma continuous_ψc : Continuous (fun z : ℝ × ℝ => ψc z.1 z.2) := by
  have hm : Continuous (fun z : ℝ × ℝ => max z.2 (11 / 10 : ℝ)) :=
    continuous_snd.max continuous_const
  have h1 : ∀ z : ℝ × ℝ, max z.2 (11 / 10 : ℝ) - 1 ≠ 0 := fun z =>
    (show (0:ℝ) < max z.2 (11 / 10) - 1 by linarith [le_max_right z.2 (11 / 10 : ℝ)]).ne'
  have h0 : ∀ z : ℝ × ℝ, max z.2 (11 / 10 : ℝ) ≠ 0 := fun z =>
    (show (0:ℝ) < max z.2 (11 / 10) by linarith [le_max_right z.2 (11 / 10 : ℝ)]).ne'
  show Continuous (fun z : ℝ × ℝ => 28 / 5 * Real.log (max z.2 (11 / 10) - 1)
    + 27 / max z.2 (11 / 10) - z.1 * max z.2 (11 / 10))
  exact ((continuous_const.mul ((hm.sub continuous_const).log h1)).add
    (continuous_const.div hm h0)).sub (continuous_fst.mul hm)

lemma continuous_ψc_left (p : ℝ) : Continuous (ψc p) := by
  have hm : Continuous (fun x : ℝ => max x (11 / 10 : ℝ)) := continuous_id.max continuous_const
  have h1 : ∀ x : ℝ, max x (11 / 10 : ℝ) - 1 ≠ 0 := fun x =>
    (show (0:ℝ) < max x (11 / 10) - 1 by linarith [le_max_right x (11 / 10 : ℝ)]).ne'
  have h0 : ∀ x : ℝ, max x (11 / 10 : ℝ) ≠ 0 := fun x =>
    (show (0:ℝ) < max x (11 / 10) by linarith [le_max_right x (11 / 10 : ℝ)]).ne'
  show Continuous (fun x : ℝ => 28 / 5 * Real.log (max x (11 / 10) - 1)
    + 27 / max x (11 / 10) - p * max x (11 / 10))
  exact ((continuous_const.mul ((hm.sub continuous_const).log h1)).add
    (continuous_const.div hm h0)).sub (continuous_const.mul hm)

/-- Gas-window maximum minus liquid-window maximum of `ψ π`. -/
noncomputable def Dgap (p : ℝ) : ℝ :=
  sSup (ψc p '' Icc 23 30) - sSup (ψc p '' Icc (11 / 10) (149 / 100))

lemma continuous_Dgap : Continuous Dgap := by
  show Continuous (fun p => sSup (ψc p '' Icc 23 30) - sSup (ψc p '' Icc (11 / 10) (149 / 100)))
  exact ((isCompact_Icc (a := (23:ℝ)) (b := 30)).continuous_sSup (f := ψc) continuous_ψc).sub
    ((isCompact_Icc (a := (11 / 10 : ℝ)) (b := 149 / 100)).continuous_sSup (f := ψc) continuous_ψc)

lemma exists_max (p a b : ℝ) (ha : 11 / 10 ≤ a) (hab : a ≤ b) :
    ∃ x ∈ Icc a b, sSup (ψc p '' Icc a b) = ψ p x ∧ ∀ y ∈ Icc a b, ψ p y ≤ ψ p x := by
  obtain ⟨x, hx, h1, h2⟩ := (isCompact_Icc (a := a) (b := b)).exists_sSup_image_eq_and_ge
    (nonempty_Icc.2 hab) (continuous_ψc_left p).continuousOn
  refine ⟨x, hx, ?_, fun y hy => ?_⟩
  · rw [h1, ψc_eq (le_trans ha hx.1)]
  · have := h2 y hy
    rwa [ψc_eq (le_trans ha hy.1), ψc_eq (le_trans ha hx.1)] at this

lemma le_sSup_ψ (p a b z : ℝ) (ha : 11 / 10 ≤ a) (hz : z ∈ Icc a b) :
    ψ p z ≤ sSup (ψc p '' Icc a b) := by
  rw [← ψc_eq (p := p) (le_trans ha hz.1)]
  exact le_csSup ((isCompact_Icc (a := a) (b := b)).bddAbove_image
    (continuous_ψc_left p).continuousOn) (mem_image_of_mem _ hz)

lemma gL_anti : AntitoneOn g (Icc (11 / 10) (149 / 100)) :=
  g_anti (by norm_num) (fun x hx => (q_pos_low (by linarith [hx.1]) hx.2).le)

lemma gR_anti : AntitoneOn g (Icc 23 30) :=
  g_anti (by norm_num) (fun x hx => (q_pos_high hx.1).le)

/-- Left of a point `d` where `g` stays above `g d`: `ψ p x ≤ ψ p d + (p − g d)(d − x)`. -/
lemma ψ_le_of_ge {p x d : ℝ} (hx : 1 < x) (hxd : x ≤ d) (h : ∀ y ∈ Icc x d, g d ≤ g y) :
    ψ p x ≤ ψ p d + (p - g d) * (d - x) := by
  have m := ψ_mono (p := g d) hx h ⟨le_rfl, hxd⟩ ⟨hxd, le_rfl⟩ hxd
  have key : ψ p x - ψ p d - (p - g d) * (d - x) = ψ (g d) x - ψ (g d) d := by
    unfold ψ; ring
  linarith

/-- Right of a point `d` where `g` stays below `g d`: `ψ p x ≤ ψ p d − (p − g d)(x − d)`. -/
lemma ψ_le_of_le {p x d : ℝ} (hd : 1 < d) (hdx : d ≤ x) (h : ∀ y ∈ Icc d x, g y ≤ g d) :
    ψ p x ≤ ψ p d - (p - g d) * (x - d) := by
  have m := ψ_anti (p := g d) hd h ⟨le_rfl, hdx⟩ ⟨hdx, le_rfl⟩ hdx
  have key : ψ p x - ψ p d + (p - g d) * (x - d) = ψ (g d) x - ψ (g d) d := by
    unfold ψ; ring
  linarith

/-- A maximizer of `ψ π` on the liquid window lies in `[1.4, 1.40158]`. -/
lemma left_loc {p x : ℝ} (hp1 : 40091 / 200000 ≤ p) (hp2 : p ≤ 40093 / 200000)
    (hx : x ∈ Icc (11 / 10 : ℝ) (149 / 100))
    (hm : ∀ y ∈ Icc (11 / 10 : ℝ) (149 / 100), ψ p y ≤ ψ p x) :
    7 / 5 ≤ x ∧ x ≤ 70079 / 50000 := by
  have gc : 40093 / 200000 < g (7 / 5) := by unfold g; norm_num
  have gd : g (70079 / 50000) < 40091 / 200000 := num_lo.2.1
  have c_mem : (7 / 5 : ℝ) ∈ Icc (11 / 10 : ℝ) (149 / 100) := ⟨by norm_num, by norm_num⟩
  have d_mem : (70079 / 50000 : ℝ) ∈ Icc (11 / 10 : ℝ) (149 / 100) := ⟨by norm_num, by norm_num⟩
  constructor
  · by_contra hlt
    have hlt' : x < 7 / 5 := not_le.1 hlt
    have b := ψ_le_of_ge (p := p) (by linarith [hx.1]) hlt'.le (fun y hy =>
      gL_anti ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩ c_mem hy.2)
    have := mul_neg_of_neg_of_pos (by linarith : p - g (7 / 5) < 0)
      (by linarith : (0:ℝ) < 7 / 5 - x)
    linarith [hm _ c_mem]
  · by_contra hgt
    have hgt' : 70079 / 50000 < x := not_le.1 hgt
    have b := ψ_le_of_le (p := p) (by norm_num) hgt'.le (fun y hy =>
      gL_anti d_mem ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩ hy.1)
    have := mul_pos (by linarith : (0:ℝ) < p - g (70079 / 50000))
      (by linarith : (0:ℝ) < x - 70079 / 50000)
    linarith [hm _ d_mem]

/-- A maximizer of `ψ π` on the gas window lies in `[23.43247, 23.44]`. -/
lemma right_loc {p x : ℝ} (hp1 : 40091 / 200000 ≤ p) (hp2 : p ≤ 40093 / 200000)
    (hx : x ∈ Icc (23 : ℝ) 30) (hm : ∀ y ∈ Icc (23 : ℝ) 30, ψ p y ≤ ψ p x) :
    2343247 / 100000 ≤ x ∧ x ≤ 586 / 25 := by
  have gc : 40093 / 200000 < g (2343247 / 100000) := num_hi.2.1
  have gd : g (586 / 25) < 40091 / 200000 := by unfold g; norm_num
  have c_mem : (2343247 / 100000 : ℝ) ∈ Icc (23 : ℝ) 30 := ⟨by norm_num, by norm_num⟩
  have d_mem : (586 / 25 : ℝ) ∈ Icc (23 : ℝ) 30 := ⟨by norm_num, by norm_num⟩
  constructor
  · by_contra hlt
    have hlt' : x < 2343247 / 100000 := not_le.1 hlt
    have b := ψ_le_of_ge (p := p) (by linarith [hx.1]) hlt'.le (fun y hy =>
      gR_anti ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩ c_mem hy.2)
    have := mul_neg_of_neg_of_pos (by linarith : p - g (2343247 / 100000) < 0)
      (by linarith : (0:ℝ) < 2343247 / 100000 - x)
    linarith [hm _ c_mem]
  · by_contra hgt
    have hgt' : 586 / 25 < x := not_le.1 hgt
    have b := ψ_le_of_le (p := p) (by norm_num) hgt'.le (fun y hy =>
      gR_anti d_mem ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩ hy.1)
    have := mul_pos (by linarith : (0:ℝ) < p - g (586 / 25))
      (by linarith : (0:ℝ) < x - 586 / 25)
    linarith [hm _ d_mem]

/-- An interior maximizer of `ψ π` is a point of the isotherm at pressure `π`. -/
lemma crit_of_max {p x a b : ℝ} (ha : 1 < a) (hax : a < x) (hxb : x < b)
    (hm : ∀ y ∈ Icc a b, ψ p y ≤ ψ p x) : g x = p := by
  have hloc : IsLocalMax (ψ p) x := (isMaxOn_iff.2 hm).isLocalMax (Icc_mem_nhds hax hxb)
  have := hloc.hasDerivAt_eq_zero (hasDerivAt_ψ p (by linarith))
  linarith

lemma Dgap_lo : 0 < Dgap (40091 / 200000) := by
  obtain ⟨x, hx, hS, hm⟩ := exists_max (40091 / 200000) (11 / 10) (149 / 100) le_rfl (by norm_num)
  obtain ⟨c1, d1⟩ := left_loc le_rfl (by norm_num) hx hm
  have hg : g x = 40091 / 200000 :=
    crit_of_max (by norm_num : (1:ℝ) < 11 / 10) (by linarith) (by linarith) hm
  have hx0 : (1401579 / 1000000 : ℝ) ≤ x := by
    by_contra h
    have h' := not_le.1 h
    have := gL_anti hx ⟨by norm_num, by norm_num⟩ h'.le
    linarith [num_lo.1]
  have hb := ψ_le_of_ge (p := 40091 / 200000) (by linarith) d1 (fun y hy =>
    gL_anti ⟨by linarith [hy.1], by linarith [hy.2]⟩ ⟨by norm_num, by norm_num⟩ hy.2)
  have hprod := mul_le_mul_of_nonneg_left
    (by linarith : (70079 / 50000 : ℝ) - x ≤ 70079 / 50000 - 1401579 / 1000000)
    (by linarith [num_lo.2.1] : (0:ℝ) ≤ 40091 / 200000 - g (70079 / 50000))
  have hcomm : (40091 / 200000 - g (70079 / 50000)) * (70079 / 50000 - 1401579 / 1000000)
      = (70079 / 50000 - 1401579 / 1000000) * (40091 / 200000 - g (70079 / 50000)) :=
    mul_comm _ _
  have hK := K_lo
  have hR := le_sSup_ψ (40091 / 200000) 23 30 (2343391 / 100000) (by norm_num)
    ⟨by norm_num, by norm_num⟩
  unfold Dgap
  rw [hS]
  linarith

lemma Dgap_hi : Dgap (40093 / 200000) < 0 := by
  obtain ⟨y, hy, hS, hm⟩ := exists_max (40093 / 200000) 23 30 (by norm_num) (by norm_num)
  obtain ⟨c2, d2⟩ := right_loc (by norm_num) le_rfl hy hm
  have hg : g y = 40093 / 200000 :=
    crit_of_max (by norm_num : (1:ℝ) < 23) (by linarith) (by linarith) hm
  have hy0 : y ≤ 146453 / 6250 := by
    by_contra h
    have h' := not_le.1 h
    have := gR_anti ⟨by norm_num, by norm_num⟩ hy h'.le
    linarith [num_hi.2.2]
  have hb := ψ_le_of_ge (p := 40093 / 200000) (by linarith) hy0 (fun z hz =>
    gR_anti ⟨by linarith [hz.1, hy.1], by linarith [hz.2]⟩ ⟨by norm_num, by norm_num⟩ hz.2)
  have hprod := mul_le_mul_of_nonneg_left
    (by linarith : (146453 / 6250 : ℝ) - y ≤ 146453 / 6250 - 2343247 / 100000)
    (by linarith [num_hi.2.2] : (0:ℝ) ≤ 40093 / 200000 - g (146453 / 6250))
  have hcomm : (40093 / 200000 - g (146453 / 6250)) * (146453 / 6250 - 2343247 / 100000)
      = (146453 / 6250 - 2343247 / 100000) * (40093 / 200000 - g (146453 / 6250)) :=
    mul_comm _ _
  have hK := K_hi
  have hL := le_sSup_ψ (40093 / 200000) (11 / 10) (149 / 100) (1401579 / 1000000) le_rfl
    ⟨by norm_num, by norm_num⟩
  unfold Dgap
  rw [hS]
  linarith

/-- **Existence.** The reduced vdW isotherm at `T = 0.7 T_c` has a Maxwell coexistence state. -/
theorem reduced_exists :
    ∃ x₁ x₂ p, 1 < x₁ ∧ x₁ < x₂ ∧ g x₁ = p ∧ g x₂ = p ∧ ψ p x₁ = ψ p x₂ := by
  obtain ⟨p, hp, hD⟩ := intermediate_value_Icc' (by norm_num : (40091 / 200000 : ℝ) ≤ 40093 / 200000)
    continuous_Dgap.continuousOn
    (show (0:ℝ) ∈ Icc (Dgap (40093 / 200000)) (Dgap (40091 / 200000)) from ⟨Dgap_hi.le, Dgap_lo.le⟩)
  obtain ⟨x, hx, hSx, hmx⟩ := exists_max p (11 / 10) (149 / 100) le_rfl (by norm_num)
  obtain ⟨y, hy, hSy, hmy⟩ := exists_max p 23 30 (by norm_num) (by norm_num)
  obtain ⟨c1, d1⟩ := left_loc hp.1 hp.2 hx hmx
  obtain ⟨c2, d2⟩ := right_loc hp.1 hp.2 hy hmy
  have hgx := crit_of_max (by norm_num : (1:ℝ) < 11 / 10) (by linarith) (by linarith) hmx
  have hgy := crit_of_max (by norm_num : (1:ℝ) < 23) (by linarith) (by linarith) hmy
  unfold Dgap at hD
  rw [hSx, hSy] at hD
  exact ⟨x, y, p, by linarith [hx.1], by linarith [hx.2, hy.1], hgx, hgy, by linarith⟩

/-! ## Acentric factor from the pressure window -/

lemma acentric_window {p : ℝ} (h1 : 40091 / 200000 ≤ p) (h2 : p ≤ 40093 / 200000) :
    RoundsTo (-Real.logb 10 p - 1) (-0.3020) 4 := by
  have hp : 0 < p := by linarith
  have h5 : 0 < 5 * p := by linarith
  -- 3 log 10 = 10 log 2 + log (1 − 3/128), since 1000 = 2¹⁰ (1 − 3/128)
  have hL3 : Real.log ((10:ℝ) ^ 3) = Real.log ((2:ℝ) ^ 10 * (1 - 3 / 128)) := by norm_num
  rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hL3
  push_cast at hL3
  have hs := log_series (3 / 128) (by norm_num) (by norm_num) 4
  rw [abs_le] at hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  norm_num at hs hL3
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  -- log p = log 2 + log (5p) − log 10
  have hlp : Real.log p = Real.log 2 + Real.log (5 * p) - Real.log 10 := by
    have e1 : Real.log (10 * p) = Real.log 10 + Real.log p := Real.log_mul (by norm_num) hp.ne'
    have e2 : Real.log (10 * p) = Real.log 2 + Real.log (5 * p) := by
      rw [show (10:ℝ) * p = 2 * (5 * p) by ring, Real.log_mul (by norm_num) h5.ne']
    linarith
  have u1 : Real.log (5 * p) ≤ 5 * p - 1 := Real.log_le_sub_one_of_pos h5
  have u2 : Real.log (40091 / 40000) ≤ Real.log (5 * p) :=
    Real.log_le_log (by norm_num) (by linarith)
  have u3 : 1 - (40091 / 40000 : ℝ)⁻¹ ≤ Real.log (40091 / 40000) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  norm_num at u3
  have hL0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have A : -69805 / 100000 * Real.log 10 ≤ Real.log p := by linarith
  have B : Real.log p ≤ -69795 / 100000 * Real.log 10 := by linarith
  have A' : -69805 / 100000 ≤ Real.log p / Real.log 10 := (le_div_iff₀ hL0).2 A
  have B' : Real.log p / Real.log 10 ≤ -69795 / 100000 := (div_le_iff₀ hL0).2 B
  unfold RoundsTo Real.logb
  generalize Real.log p / Real.log 10 = r at A' B' ⊢
  rw [abs_le]
  constructor <;> norm_num <;> linarith

/-! ## Back to molar volumes and pressures -/

lemma cubicP_eq_g (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) {v : ℝ} (hv : b < v) :
    cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b))) v = a / (27 * b ^ 2) * g (v / b) := by
  have hb0 : b ≠ 0 := hb.ne'
  have h1 : v - b ≠ 0 := by linarith
  have h2 : v ≠ 0 := by linarith
  have h3 : v / b - 1 ≠ 0 := by
    rw [div_sub_one hb0]; exact div_ne_zero h1 hb0
  unfold cubicP g
  rw [div_sub_one hb0]
  field_simp
  ring

lemma integral_cubicP (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) {vl vg : ℝ}
    (hl : b < vl) (hlg : vl < vg) :
    ∫ v in vl..vg, cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b))) v
      = a / (27 * b ^ 2) * (b * (ψ 0 (vg / b) - ψ 0 (vl / b))) := by
  have hb0 : b ≠ 0 := hb.ne'
  have h1 : 1 < vl / b := by rw [lt_div_iff₀ hb]; linarith
  have h12 : vl / b < vg / b := div_lt_div_of_pos_right hlg hb
  rw [intervalIntegral.integral_congr (g := fun v => a / (27 * b ^ 2) * g (v / b))
    (fun v hv => by
      rw [Set.uIcc_of_le hlg.le] at hv
      exact cubicP_eq_g R a b hR ha hb (by linarith [hv.1]))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div (fun x => g x) hb0]
  congr 1
  rw [smul_eq_mul]
  congr 1
  have hd : ∀ x ∈ Set.uIcc (vl / b) (vg / b), HasDerivAt (ψ 0) (g x - 0) x := by
    intro x hx
    rw [Set.uIcc_of_le h12.le] at hx
    exact hasDerivAt_ψ 0 (by linarith [hx.1])
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_g (t := vg / b) h1).sub continuousOn_const |>.intervalIntegrable_of_Icc h12.le)
  simpa using this

end Checked.Chemistry.CoexistenceReduced
