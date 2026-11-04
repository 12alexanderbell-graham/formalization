import Mathlib
import Work.Chemistry.RKReduced
import Checked.Records.Basic
import Checked.Chemistry.CubicEOS
import Checked.Chemistry.Coexistence

/-!
# Existence of the Redlich–Kwong coexistence state at T = 0.7 T_c (run 2026-11-04T1828Z)

Route of `Checked.Chemistry.CoexistenceExists` (van der Waals), with the reduced temperature
`θ` a parameter in the certified interval: for each pressure `π`, `M₁(π) = max ψ θ π` on the
liquid window `[1.1, 1.5]` and `M₂(π) = max ψ θ π` on the gas window `[60, 110]` are continuous
in `π`; for `π ∈ [0.0012845, 0.0012849]` every maximizer is interior (`left_loc`,
`right_loc`), hence a point of the isotherm; at `π = 0.0012845` the gas maximum is higher
(`K_lo`), at `π = 0.0012849` the liquid maximum is higher (`K_hi`); the intermediate value
theorem gives equal maxima. Brackets: `runs/2026-11-04T1828Z/scripts/gen_rk_exists.py`.
-/

namespace Work.Chemistry.RKExists

open Real Set Work.Chemistry.RKReduced

section
variable {θ : ℝ}

/-- `ψ θ` with the volume clamped to `x ≥ 1.1`. -/
noncomputable def ψc (θ p x : ℝ) : ℝ := ψ θ p (max x (11 / 10))

lemma ψc_eq {p x : ℝ} (h : 11 / 10 ≤ x) : ψc θ p x = ψ θ p x := by
  unfold ψc; rw [max_eq_left h]

lemma continuous_ψc : Continuous (fun z : ℝ × ℝ => ψc θ z.1 z.2) := by
  have hm : Continuous (fun z : ℝ × ℝ => max z.2 (11 / 10 : ℝ)) :=
    continuous_snd.max continuous_const
  have h1 : ∀ z : ℝ × ℝ, max z.2 (11 / 10 : ℝ) - 1 ≠ 0 := fun z =>
    (show (0:ℝ) < max z.2 (11 / 10) - 1 by linarith [le_max_right z.2 (11 / 10 : ℝ)]).ne'
  have h0 : ∀ z : ℝ × ℝ, max z.2 (11 / 10 : ℝ) ≠ 0 := fun z =>
    (show (0:ℝ) < max z.2 (11 / 10) by linarith [le_max_right z.2 (11 / 10 : ℝ)]).ne'
  have h2 : ∀ z : ℝ × ℝ, max z.2 (11 / 10 : ℝ) + 1 ≠ 0 := fun z =>
    (show (0:ℝ) < max z.2 (11 / 10) + 1 by linarith [le_max_right z.2 (11 / 10 : ℝ)]).ne'
  show Continuous (fun z : ℝ × ℝ => θ * Real.log (max z.2 (11 / 10) - 1)
    + (Real.log (max z.2 (11 / 10) + 1) - Real.log (max z.2 (11 / 10))) - z.1 * max z.2 (11 / 10))
  exact ((continuous_const.mul ((hm.sub continuous_const).log h1)).add
    (((hm.add continuous_const).log h2).sub (hm.log h0))).sub (continuous_fst.mul hm)

lemma continuous_ψc_left (p : ℝ) : Continuous (ψc θ p) :=
  continuous_ψc.comp (continuous_const.prodMk continuous_id)

/-- Gas-window maximum minus liquid-window maximum of `ψ θ π`. -/
noncomputable def Dgap (θ p : ℝ) : ℝ :=
  sSup (ψc θ p '' Icc 60 110) - sSup (ψc θ p '' Icc (11 / 10) (3 / 2))

lemma continuous_Dgap : Continuous (Dgap θ) := by
  show Continuous (fun p => sSup (ψc θ p '' Icc 60 110) - sSup (ψc θ p '' Icc (11 / 10) (3 / 2)))
  exact ((isCompact_Icc (a := (60:ℝ)) (b := 110)).continuous_sSup
      (f := fun p x => ψc θ p x) continuous_ψc).sub
    ((isCompact_Icc (a := (11 / 10 : ℝ)) (b := 3 / 2)).continuous_sSup
      (f := fun p x => ψc θ p x) continuous_ψc)

lemma exists_max (p a b : ℝ) (ha : 11 / 10 ≤ a) (hab : a ≤ b) :
    ∃ x ∈ Icc a b, sSup (ψc θ p '' Icc a b) = ψ θ p x ∧ ∀ y ∈ Icc a b, ψ θ p y ≤ ψ θ p x := by
  obtain ⟨x, hx, h1, h2⟩ := (isCompact_Icc (a := a) (b := b)).exists_sSup_image_eq_and_ge
    (nonempty_Icc.2 hab) (continuous_ψc_left (θ := θ) p).continuousOn
  refine ⟨x, hx, ?_, fun y hy => ?_⟩
  · rw [h1, ψc_eq (le_trans ha hx.1)]
  · have := h2 y hy
    rwa [ψc_eq (le_trans ha hy.1), ψc_eq (le_trans ha hx.1)] at this

lemma le_sSup_ψ (p a b z : ℝ) (ha : 11 / 10 ≤ a) (hz : z ∈ Icc a b) :
    ψ θ p z ≤ sSup (ψc θ p '' Icc a b) := by
  rw [← ψc_eq (θ := θ) (p := p) (le_trans ha hz.1)]
  exact le_csSup ((isCompact_Icc (a := a) (b := b)).bddAbove_image
    (continuous_ψc_left p).continuousOn) (mem_image_of_mem _ hz)

/-- Left of a point `d` where `g` stays above `g d`. -/
lemma ψ_le_of_ge {p x d : ℝ} (hx : 1 < x) (hxd : x ≤ d) (h : ∀ y ∈ Icc x d, g θ d ≤ g θ y) :
    ψ θ p x ≤ ψ θ p d + (p - g θ d) * (d - x) := by
  have m := ψ_mono (θ := θ) (p := g θ d) hx h ⟨le_rfl, hxd⟩ ⟨hxd, le_rfl⟩ hxd
  have key : ψ θ p x - ψ θ p d - (p - g θ d) * (d - x) = ψ θ (g θ d) x - ψ θ (g θ d) d := by
    unfold ψ; ring
  linarith

/-- Right of a point `d` where `g` stays below `g d`. -/
lemma ψ_le_of_le {p x d : ℝ} (hd : 1 < d) (hdx : d ≤ x) (h : ∀ y ∈ Icc d x, g θ y ≤ g θ d) :
    ψ θ p x ≤ ψ θ p d - (p - g θ d) * (x - d) := by
  have m := ψ_anti (θ := θ) (p := g θ d) hd h ⟨le_rfl, hdx⟩ ⟨hdx, le_rfl⟩ hdx
  have key : ψ θ p x - ψ θ p d + (p - g θ d) * (x - d) = ψ θ (g θ d) x - ψ θ (g θ d) d := by
    unfold ψ; ring
  linarith

lemma crit_of_max {p x a b : ℝ} (ha : 1 < a) (hax : a < x) (hxb : x < b)
    (hm : ∀ y ∈ Icc a b, ψ θ p y ≤ ψ θ p x) : g θ x = p := by
  have hloc : IsLocalMax (ψ θ p) x := (isMaxOn_iff.2 hm).isLocalMax (Icc_mem_nhds hax hxb)
  have := hloc.hasDerivAt_eq_zero (hasDerivAt_ψ θ p (by linarith))
  linarith

end

section
variable {θ : ℝ} (hθ0 : 1187001329 / 10000000000 ≤ θ) (hθ1 : θ ≤ 593500771 / 5000000000)
include hθ0 hθ1

lemma gL_anti : AntitoneOn (g θ) (Icc (11 / 10) (3 / 2)) :=
  g_anti (by norm_num) (fun x hx => (q_neg_L hθ0 hθ1 (by linarith [hx.1]) (by linarith [hx.2])).le)

lemma gR_anti : AntitoneOn (g θ) (Icc 60 110) :=
  g_anti (by norm_num) (fun x hx => (q_neg_right hθ0 hθ1 (by linarith [hx.1])).le)

lemma left_loc {p x : ℝ} (hp1 : 2569 / 2000000 ≤ p) (hp2 : p ≤ 12849 / 10000000)
    (hx : x ∈ Icc (11 / 10 : ℝ) (3 / 2))
    (hm : ∀ y ∈ Icc (11 / 10 : ℝ) (3 / 2), ψ θ p y ≤ ψ θ p x) :
    139 / 100 ≤ x ∧ x ≤ 6973967 / 5000000 := by
  have gc : 12849 / 10000000 < g θ (139 / 100) := by
    have := g_mono_θ hθ0 (x := 139 / 100) (by norm_num)
    have : (12849 / 10000000 : ℝ) < g (1187001329 / 10000000000) (139 / 100) := by norm_num [g]
    linarith
  have gd : g θ (6973967 / 5000000) < 2569 / 2000000 := (num_lo hθ0 hθ1).2.1
  have c_mem : (139 / 100 : ℝ) ∈ Icc (11 / 10 : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  have d_mem : (6973967 / 5000000 : ℝ) ∈ Icc (11 / 10 : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  constructor
  · by_contra hlt
    have hlt' : x < 139 / 100 := not_le.1 hlt
    have b := ψ_le_of_ge (θ := θ) (p := p) (by linarith [hx.1]) hlt'.le (fun y hy =>
      gL_anti hθ0 hθ1 ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩ c_mem hy.2)
    have := mul_neg_of_neg_of_pos (by linarith : p - g θ (139 / 100) < 0)
      (by linarith : (0:ℝ) < 139 / 100 - x)
    linarith [hm _ c_mem]
  · by_contra hgt
    have hgt' : 6973967 / 5000000 < x := not_le.1 hgt
    have b := ψ_le_of_le (θ := θ) (p := p) (by norm_num) hgt'.le (fun y hy =>
      gL_anti hθ0 hθ1 d_mem ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩ hy.1)
    have := mul_pos (by linarith : (0:ℝ) < p - g θ (6973967 / 5000000))
      (by linarith : (0:ℝ) < x - 6973967 / 5000000)
    linarith [hm _ d_mem]

lemma right_loc {p x : ℝ} (hp1 : 2569 / 2000000 ≤ p) (hp2 : p ≤ 12849 / 10000000)
    (hx : x ∈ Icc (60 : ℝ) 110) (hm : ∀ y ∈ Icc (60 : ℝ) 110, ψ θ p y ≤ ψ θ p x) :
    843727 / 10000 ≤ x ∧ x ≤ 87 := by
  have gc : 12849 / 10000000 < g θ (843727 / 10000) := (num_hi hθ0 hθ1).2.1
  have gd : g θ 87 < 2569 / 2000000 := by
    have := g_mono_θ hθ1 (x := 87) (by norm_num)
    have : g (593500771 / 5000000000) 87 < (2569 / 2000000 : ℝ) := by norm_num [g]
    linarith
  have c_mem : (843727 / 10000 : ℝ) ∈ Icc (60 : ℝ) 110 := ⟨by norm_num, by norm_num⟩
  have d_mem : (87 : ℝ) ∈ Icc (60 : ℝ) 110 := ⟨by norm_num, by norm_num⟩
  constructor
  · by_contra hlt
    have hlt' : x < 843727 / 10000 := not_le.1 hlt
    have b := ψ_le_of_ge (θ := θ) (p := p) (by linarith [hx.1]) hlt'.le (fun y hy =>
      gR_anti hθ0 hθ1 ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩ c_mem hy.2)
    have := mul_neg_of_neg_of_pos (by linarith : p - g θ (843727 / 10000) < 0)
      (by linarith : (0:ℝ) < 843727 / 10000 - x)
    linarith [hm _ c_mem]
  · by_contra hgt
    have hgt' : 87 < x := not_le.1 hgt
    have b := ψ_le_of_le (θ := θ) (p := p) (by norm_num) hgt'.le (fun y hy =>
      gR_anti hθ0 hθ1 d_mem ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩ hy.1)
    have := mul_pos (by linarith : (0:ℝ) < p - g θ 87)
      (by linarith : (0:ℝ) < x - 87)
    linarith [hm _ d_mem]

lemma Dgap_lo : 0 < Dgap θ (2569 / 2000000) := by
  obtain ⟨x, hx, hS, hm⟩ := exists_max (θ := θ) (2569 / 2000000) (11 / 10) (3 / 2) le_rfl (by norm_num)
  obtain ⟨c1, d1⟩ := left_loc hθ0 hθ1 le_rfl (by norm_num) hx hm
  obtain ⟨n1, n2, n3⟩ := num_lo hθ0 hθ1
  have hg : g θ x = 2569 / 2000000 :=
    crit_of_max (by norm_num : (1:ℝ) < 11 / 10) (by linarith) (by linarith) hm
  have hx0 : (3486983 / 2500000 : ℝ) ≤ x := by
    by_contra h
    have h' := not_le.1 h
    have := gL_anti hθ0 hθ1 hx ⟨by norm_num, by norm_num⟩ h'.le
    linarith
  have hb := ψ_le_of_ge (θ := θ) (p := 2569 / 2000000) (by linarith) d1 (fun y hy =>
    gL_anti hθ0 hθ1 ⟨by linarith [hy.1], by linarith [hy.2]⟩ ⟨by norm_num, by norm_num⟩ hy.2)
  have hprod := mul_le_mul_of_nonneg_left
    (by linarith : (6973967 / 5000000 : ℝ) - x ≤ 6973967 / 5000000 - 3486983 / 2500000)
    (by linarith : (0:ℝ) ≤ 2569 / 2000000 - g θ (6973967 / 5000000))
  have hcomm : (2569 / 2000000 - g θ (6973967 / 5000000)) * (6973967 / 5000000 - 3486983 / 2500000)
      = (6973967 / 5000000 - 3486983 / 2500000) * (2569 / 2000000 - g θ (6973967 / 5000000)) :=
    mul_comm _ _
  have hK := K_lo hθ0 hθ1
  have hR := le_sSup_ψ (θ := θ) (2569 / 2000000) 60 110 (844017 / 10000) (by norm_num)
    ⟨by norm_num, by norm_num⟩
  unfold Dgap
  rw [hS]
  linarith

lemma Dgap_hi : Dgap θ (12849 / 10000000) < 0 := by
  obtain ⟨y, hy, hS, hm⟩ := exists_max (θ := θ) (12849 / 10000000) 60 110 (by norm_num) (by norm_num)
  obtain ⟨c2, d2⟩ := right_loc hθ0 hθ1 (by norm_num) le_rfl hy hm
  obtain ⟨n1, n2, n3⟩ := num_hi hθ0 hθ1
  have hg : g θ y = 12849 / 10000000 :=
    crit_of_max (by norm_num : (1:ℝ) < 60) (by linarith) (by linarith) hm
  have hy0 : y ≤ 52733 / 625 := by
    by_contra h
    have h' := not_le.1 h
    have := gR_anti hθ0 hθ1 ⟨by norm_num, by norm_num⟩ hy h'.le
    linarith
  have hb := ψ_le_of_ge (θ := θ) (p := 12849 / 10000000) (by linarith) hy0 (fun z hz =>
    gR_anti hθ0 hθ1 ⟨by linarith [hz.1, hy.1], by linarith [hz.2]⟩ ⟨by norm_num, by norm_num⟩ hz.2)
  have hprod := mul_le_mul_of_nonneg_left
    (by linarith : (52733 / 625 : ℝ) - y ≤ 52733 / 625 - 843727 / 10000)
    (by linarith : (0:ℝ) ≤ 12849 / 10000000 - g θ (52733 / 625))
  have hcomm : (12849 / 10000000 - g θ (52733 / 625)) * (52733 / 625 - 843727 / 10000)
      = (52733 / 625 - 843727 / 10000) * (12849 / 10000000 - g θ (52733 / 625)) :=
    mul_comm _ _
  have hK := K_hi hθ0 hθ1
  have hL := le_sSup_ψ (θ := θ) (12849 / 10000000) (11 / 10) (3 / 2) (3486981 / 2500000) le_rfl
    ⟨by norm_num, by norm_num⟩
  unfold Dgap
  rw [hS]
  linarith

/-- **Existence** in reduced variables, for every `θ` in the certified interval. -/
theorem reduced_exists :
    ∃ x₁ x₂ p, 1 < x₁ ∧ x₁ < x₂ ∧ g θ x₁ = p ∧ g θ x₂ = p ∧ ψ θ p x₁ = ψ θ p x₂ := by
  obtain ⟨p, hp, hD⟩ := intermediate_value_Icc'
    (by norm_num : (2569 / 2000000 : ℝ) ≤ 12849 / 10000000)
    (continuous_Dgap (θ := θ)).continuousOn
    (show (0:ℝ) ∈ Icc (Dgap θ (12849 / 10000000)) (Dgap θ (2569 / 2000000)) from
      ⟨(Dgap_hi hθ0 hθ1).le, (Dgap_lo hθ0 hθ1).le⟩)
  obtain ⟨x, hx, hSx, hmx⟩ := exists_max (θ := θ) p (11 / 10) (3 / 2) le_rfl (by norm_num)
  obtain ⟨y, hy, hSy, hmy⟩ := exists_max (θ := θ) p 60 110 (by norm_num) (by norm_num)
  obtain ⟨c1, d1⟩ := left_loc hθ0 hθ1 hp.1 hp.2 hx hmx
  obtain ⟨c2, d2⟩ := right_loc hθ0 hθ1 hp.1 hp.2 hy hmy
  have hgx := crit_of_max (by norm_num : (1:ℝ) < 11 / 10) (by linarith) (by linarith) hmx
  have hgy := crit_of_max (by norm_num : (1:ℝ) < 60) (by linarith) (by linarith) hmy
  unfold Dgap at hD
  rw [hSx, hSy] at hD
  exact ⟨x, y, p, by linarith [hx.1], by linarith [hx.2, hy.1], hgx, hgy, by linarith⟩

end

/-! ## Back to molar volumes -/

open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

set_option maxHeartbeats 2000000 in
/-- The reduced temperature `θ = R (0.7 T_c) b / a(0.7 T_c)` of the RK fluid lies in the
certified interval (from the critical point). -/
lemma theta_bounds (R A b Tc vc : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc) :
    1187001329 / 10000000000 ≤ R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc)) ∧
      R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc)) ≤ 593500771 / 5000000000 := by
  have hsT : 0 < Real.sqrt Tc := Real.sqrt_pos.2 hTc
  have hac0 : 0 < A / Real.sqrt Tc := div_pos hA hsT
  have hD : 0 < vc ^ 2 + 1 * b * vc + 0 * b ^ 2 := by nlinarith
  obtain ⟨hf, hx1, -, h2, h3⟩ := reduced R (A / Real.sqrt Tc) b 1 0 Tc vc hac0 hb (by norm_num) hvc hD hc
  set ac := A / Real.sqrt Tc with hac
  set Pc := cubicP R ac b 1 0 Tc vc with hPc
  set x := vc / b with hx
  unfold critCubic at hf
  have hx1' : 0 < x - 1 := by linarith
  have hs2 : 0 < 2 * x + 1 := by linarith
  obtain ⟨lo, hi⟩ := root_bounds 1 x (38473221 / 10000000) (384732211 / 100000000) hx1
    (by linear_combination hf) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : ((x - 1) * (2 * x + 1) - (x ^ 2 + 1 * x + 0)) / ((x - 1) ^ 2 * (2 * x + 1))
      = x ^ 2 / 3 - x - 1 := by
    rw [div_eq_iff (by positivity)]; linear_combination (-2 * x ^ 2 / 3 + x) * hf
  have e3 : (x ^ 2 + 1 * x + 0) ^ 2 * ((x - 1) * (2 * x + 1) - (x ^ 2 + 1 * x + 0)) /
      ((x - 1) ^ 4 * (2 * x + 1) ^ 2) = x / 9 := by
    rw [div_eq_iff (by positivity)]
    linear_combination (-4 * x ^ 4 / 9 + x ^ 3 + 2 * x ^ 2 / 3 + x / 9) * hf
  rw [e2] at h2
  rw [e3] at h3
  have hRT : 0 < R * Tc := mul_pos hR hTc
  have hOb0 : 0 < x ^ 2 / 3 - x - 1 := by nlinarith
  have hOb1 : x ^ 2 / 3 - x - 1 ≤ (384732211 / 100000000) ^ 2 / 3 - 384732211 / 100000000 - 1 := by
    nlinarith
  have hOb2 : (38473221 / 10000000) ^ 2 / 3 - 38473221 / 10000000 - 1 ≤ x ^ 2 / 3 - x - 1 := by
    nlinarith
  have hPc0 : 0 < Pc := by
    have : b * Pc = (x ^ 2 / 3 - x - 1) * (R * Tc) := by
      rw [← h2]; field_simp
    nlinarith
  -- the coexistence isotherm
  have hsq : Real.sqrt (7 / 10 * Tc) = Real.sqrt (7 / 10) * Real.sqrt Tc :=
    Real.sqrt_mul (by norm_num) Tc
  have hS0 : (836660026 / 1000000000 : ℝ) < Real.sqrt (7 / 10) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hS1 : Real.sqrt (7 / 10) < 836660027 / 1000000000 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  set s := Real.sqrt (7 / 10) with hs
  have hs0 : 0 < s := by linarith
  have ha_eq : A / Real.sqrt (7 / 10 * Tc) = ac / s := by
    rw [hsq, hac, div_div, mul_comm]
  have ha0 : 0 < A / Real.sqrt (7 / 10 * Tc) := by rw [ha_eq]; positivity
  -- θ at 0.7 T_c
  have hK : R * Tc * b / ac = 9 * (x ^ 2 / 3 - x - 1) / x := by
    have hx0 : 0 < x := by linarith
    have e : R * Tc * b / ac = (b * Pc / (R * Tc)) / (ac * Pc / (R * Tc) ^ 2) := by
      field_simp
    rw [e, h2, h3]; field_simp
  have hθ : R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc))
      = 7 / 10 * s * (9 * (x ^ 2 / 3 - x - 1) / x) := by
    rw [ha_eq, ← hK]; field_simp
  have hKe : 9 * (x ^ 2 / 3 - x - 1) / x = 3 * x - 9 - 9 / x := by
    field_simp; ring
  have hK0 : 3 * (38473221 / 10000000) - 9 - 9 / (38473221 / 10000000) ≤ 3 * x - 9 - 9 / x := by
    have : 9 / x ≤ 9 / (38473221 / 10000000) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) lo.le
    linarith
  have hK1 : 3 * x - 9 - 9 / x ≤ 3 * (384732211 / 100000000) - 9 - 9 / (384732211 / 100000000) := by
    have : 9 / (384732211 / 100000000) ≤ 9 / x :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) hi.le
    linarith
  have hθ0 : 1187001329 / 10000000000 ≤ R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc)) := by
    rw [hθ, hKe]
    have m := mul_le_mul (le_of_lt hS0) hK0 (by norm_num) hs0.le
    have : (1187001329 / 10000000000 : ℝ) ≤ 7 / 10 * ((836660026 / 1000000000) *
        (3 * (38473221 / 10000000) - 9 - 9 / (38473221 / 10000000))) := by norm_num
    nlinarith
  have hθ1 : R * (7 / 10 * Tc) * b / (A / Real.sqrt (7 / 10 * Tc)) ≤ 593500771 / 5000000000 := by
    rw [hθ, hKe]
    have hK' : 0 ≤ 3 * x - 9 - 9 / x := by rw [← hKe]; positivity
    have m := mul_le_mul (le_of_lt hS1) hK1 hK' (by norm_num)
    have : 7 / 10 * ((836660027 / 1000000000) *
        (3 * (384732211 / 100000000) - 9 - 9 / (384732211 / 100000000))) ≤ (593500771 / 5000000000 : ℝ) := by
      norm_num
    nlinarith
  exact ⟨hθ0, hθ1⟩

/-- Core of `Work.Chemistry.RKAcentric.rk_coexistence_exists` (same statement). -/
theorem rk_exists_core (R A b Tc vc : ℝ) (hR : 0 < R) (hA : 0 < A) (hb : 0 < b)
    (hTc : 0 < Tc) (hvc : b < vc)
    (hc : IsCriticalIsotherm (cubicP R (A / Real.sqrt Tc) b 1 0 Tc) vc) :
    ∃ vl vg ps, b < vl ∧
      IsMaxwellCoexistence (cubicP R (A / Real.sqrt (7 / 10 * Tc)) b 1 0 (7 / 10 * Tc)) vl vg ps ∧
      RoundsTo (ps / cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc) 0.087 3 ∧
      RoundsTo (acentric ps (cubicP R (A / Real.sqrt Tc) b 1 0 Tc vc)) 0.058 3 := by
  obtain ⟨t0, t1⟩ := theta_bounds R A b Tc vc hR hA hb hTc hvc hc
  have ha0 : 0 < A / Real.sqrt (7 / 10 * Tc) :=
    div_pos hA (Real.sqrt_pos.2 (by positivity))
  set a := A / Real.sqrt (7 / 10 * Tc) with ha
  set T := 7 / 10 * Tc with hT
  obtain ⟨x₁, x₂, p, h1, h12, hg1, hg2, hψ⟩ := reduced_exists (θ := R * T * b / a) t0 t1
  have hb0 : b ≠ 0 := hb.ne'
  have hK : 0 < a / b ^ 2 := by positivity
  have hl : b < b * x₁ := by nlinarith
  have hlg : b * x₁ < b * x₂ := mul_lt_mul_of_pos_left h12 hb
  have hM : IsMaxwellCoexistence (cubicP R a b 1 0 T) (b * x₁) (b * x₂) (a / b ^ 2 * p) := by
    refine ⟨hlg, ?_, ?_, ?_⟩
    · rw [cubicP_eq_g R a b T ha0 hb hl, mul_div_cancel_left₀ _ hb0, hg1]
    · rw [cubicP_eq_g R a b T ha0 hb (by linarith), mul_div_cancel_left₀ _ hb0, hg2]
    · rw [integral_cubicP R a b T ha0 hb hl hlg, mul_div_cancel_left₀ _ hb0,
        mul_div_cancel_left₀ _ hb0]
      have key : ψ (R * T * b / a) 0 x₂ - ψ (R * T * b / a) 0 x₁ = p * (x₂ - x₁) := by
        unfold ψ at hψ ⊢
        linear_combination -1 * hψ
      rw [key]
      ring
  obtain ⟨r1, r2⟩ := rk_unique_core R A b Tc vc (b * x₁) (b * x₂) (a / b ^ 2 * p)
    hR hA hb hTc hvc hc hl hM
  exact ⟨b * x₁, b * x₂, a / b ^ 2 * p, hl, hM, r1, r2⟩

end Work.Chemistry.RKExists
