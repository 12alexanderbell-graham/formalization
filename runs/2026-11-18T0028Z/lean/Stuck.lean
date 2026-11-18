import Checked.Trust.NecessityAP

namespace Checked.Trust.NCAQ

open Set Filter Topology MeasureTheory Real
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

/-- The bounce model with negative matter density, held at its minimum for `s ≤ 0`:
`a(s) = cosh(max s 0)^{2/3}`. -/
noncomputable def ca (s : ℝ) : ℝ := Real.cosh (max s 0) ^ (2 / 3 : ℝ)

noncomputable def cb (s : ℝ) : ℝ := Real.cosh s ^ (2 / 3 : ℝ)

theorem cb_hasDerivAt (s : ℝ) :
    HasDerivAt cb (Real.sinh s * (2 / 3) * Real.cosh s ^ ((2 / 3 : ℝ) - 1)) s :=
  (Real.hasDerivAt_cosh s).rpow_const (Or.inl (Real.cosh_pos s).ne')

theorem ca_eq_cb (s : ℝ) (hs : 0 ≤ s) : ca s = cb s := by
  simp [ca, cb, max_eq_left hs]

theorem ca_eq_one (s : ℝ) (hs : s ≤ 0) : ca s = 1 := by
  simp [ca, max_eq_right hs]

theorem ca_hasDerivAt_pos (s : ℝ) (hs : 0 < s) :
    HasDerivAt ca (Real.sinh s * (2 / 3) * Real.cosh s ^ ((2 / 3 : ℝ) - 1)) s := by
  apply (cb_hasDerivAt s).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hs] with x hx
  exact ca_eq_cb x hx.le

theorem ca_hasDerivAt_nonpos (s : ℝ) (hs : s ≤ 0) : HasDerivAt ca 0 s := by
  rcases lt_or_eq_of_le hs with hlt | rfl
  · apply (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hlt] with x hx
    exact ca_eq_one x hx.le
  · have h1 : HasDerivWithinAt ca 0 (Iic 0) 0 := by
      apply (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (1 : ℝ)).congr
      · intro x hx; exact ca_eq_one x hx
      · exact ca_eq_one 0 le_rfl
    have h2 : HasDerivWithinAt ca 0 (Ici 0) 0 := by
      have := (cb_hasDerivAt 0).hasDerivWithinAt (s := Ici 0)
      simp only [Real.sinh_zero, zero_mul] at this
      apply this.congr
      · intro x hx; exact ca_eq_cb x hx
      · exact ca_eq_cb 0 le_rfl
    have := h1.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

theorem ca_pos (s : ℝ) : 0 < ca s := Real.rpow_pos_of_pos (Real.cosh_pos _) _

theorem ca_hubble_pos (s : ℝ) (hs : 0 < s) :
    hubble ca s = 2 / 3 * (Real.sinh s / Real.cosh s) := by
  have hC := Real.cosh_pos s
  unfold hubble
  rw [(ca_hasDerivAt_pos s hs).deriv, ca_eq_cb s hs.le]
  simp only [cb]
  rw [Real.rpow_sub hC, Real.rpow_one]
  have : 0 < Real.cosh s ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hC _
  field_simp

theorem ca_hubble_nonpos (s : ℝ) (hs : s ≤ 0) : hubble ca s = 0 := by
  unfold hubble; rw [(ca_hasDerivAt_nonpos s hs).deriv]; simp

theorem cube23' (x : ℝ) (hx : 0 < x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num

/-- Observation time `t₀ = arsinh 1`: `cosh t₀ = √2`, `sinh t₀ = 1`. -/
noncomputable def T₀ : ℝ := Real.arsinh 1

theorem T₀_pos : 0 < T₀ := Real.arsinh_pos_iff.2 one_pos

theorem cosh_T₀ : Real.cosh T₀ = √2 := by
  rw [T₀, Real.cosh_arsinh]; norm_num

theorem sinh_T₀ : Real.sinh T₀ = 1 := by rw [T₀, Real.sinh_arsinh]

theorem ca_z3 (s : ℝ) : (1 + redshift ca T₀ s) ^ 3 = 2 / Real.cosh (max s 0) ^ 2 := by
  unfold redshift
  rw [show 1 + (ca T₀ / ca s - 1) = ca T₀ / ca s by ring, div_pow]
  simp only [ca]
  rw [cube23' _ (Real.cosh_pos _), cube23' _ (Real.cosh_pos _), max_eq_left T₀_pos.le, cosh_T₀,
    Real.sq_sqrt (by norm_num)]

theorem ca_H0 : hubble ca T₀ = 2 / 3 * (1 / √2) := by
  rw [ca_hubble_pos T₀ T₀_pos, sinh_T₀, cosh_T₀]

theorem ca_law (s : ℝ) :
    hubble ca s = hubble ca T₀ * √((-1) * (1 + redshift ca T₀ s) ^ 3 + 1 - (-1)) := by
  rw [ca_z3, ca_H0]
  rcases le_or_gt s 0 with hs | hs
  · rw [ca_hubble_nonpos s hs, max_eq_right hs, Real.cosh_zero]; norm_num
  · rw [ca_hubble_pos s hs, max_eq_left hs.le]
    have hC := Real.cosh_pos s
    have hS : 0 < Real.sinh s := Real.sinh_pos_iff.2 hs
    have e : (-1) * (2 / Real.cosh s ^ 2) + 1 - (-1) = (√2 * (Real.sinh s / Real.cosh s)) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
      have := Real.cosh_sq_sub_sinh_sq s
      field_simp
      nlinarith
    rw [e, Real.sqrt_sq (by positivity)]
    have : (0:ℝ) < √2 := by positivity
    field_simp

theorem ca_cont : Continuous ca := by
  have : Continuous fun s : ℝ => Real.cosh (max s 0) := by fun_prop
  exact this.rpow_const (fun _ => Or.inl (Real.cosh_pos _).ne')

/-- Without `0 ≤ Ω`: at `Ω = -1` the scale factor may rest at its bounce for any length of time
(Hubble rate zero, which the law allows where `Ω(1+z)³ + 1 − Ω = 0`), so the comoving distance grows
with that time while the right side of the bridge does not change. -/
theorem lumDistFlat_flatLCDM_h1 : necessity% Checked.Cosmography.B1.lumDistFlat_flatLCDM 1 := by
  by_contra hcon
  push Not at hcon
  have hp : ∀ t, ∀ s ∈ Set.Icc t T₀, 0 < ca s := fun _ s _ => ca_pos s
  have hd : ∀ t, ∀ s ∈ Set.Icc t T₀, DifferentiableAt ℝ ca s := fun _ s _ => by
    rcases le_or_gt s 0 with hs | hs
    · exact (ca_hasDerivAt_nonpos s hs).differentiableAt
    · exact (ca_hasDerivAt_pos s hs).differentiableAt
  have hH₀ : 0 < hubble ca T₀ := by rw [ca_H0]; positivity
  have h1 := hcon (-1) (by norm_num) ca (-1) T₀ (by linarith [T₀_pos]) (hp _) (hd _) hH₀
    (fun s _ => ca_law s)
  have h2 := hcon (-1) (by norm_num) ca (-2) T₀ (by linarith [T₀_pos]) (hp _) (hd _) hH₀
    (fun s _ => ca_law s)
  have e1 : ca (-1) = 1 := ca_eq_one _ (by norm_num)
  have e2 : ca (-2) = 1 := ca_eq_one _ (by norm_num)
  have hz : redshift ca T₀ (-1) = redshift ca T₀ (-2) := by unfold redshift; rw [e1, e2]
  rw [e2, ← hz] at h2
  rw [e1] at h1
  have hsplit : comoving ca T₀ (-2) = (∫ s in (-2:ℝ)..(-1), 1 / ca s) + comoving ca T₀ (-1) := by
    unfold comoving
    have hc : Continuous fun s => 1 / ca s :=
      continuous_const.div ca_cont (fun s => (ca_pos s).ne')
    exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  have hI : (∫ s in (-2:ℝ)..(-1), 1 / ca s) = 1 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) (fun s hs => by
      rw [uIcc_of_le (by norm_num)] at hs
      simp only; rw [ca_eq_one s (by linarith [hs.2])]; norm_num)]
    norm_num
  have hz1 : 0 < 1 + redshift ca T₀ (-1) := by
    unfold redshift; rw [e1]; simp [ca_pos]
  have hL : lumDistFlat ca T₀ (-2) = lumDistFlat ca T₀ (-1) + ca T₀ * (1 + redshift ca T₀ (-1)) := by
    unfold lumDistFlat; rw [hsplit, hI, ← hz]; ring
  have := mul_pos (ca_pos T₀) hz1
  linarith

end Checked.Trust.NCAQ
