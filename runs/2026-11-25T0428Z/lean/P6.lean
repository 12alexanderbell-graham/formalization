namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (lam U V Hyp hyp_of U_deriv V_deriv lam_deriv lam_eq_UV phi_neg
  right_gt right_lt left_lt left_gt)

section
variable {w φ : ℝ → ℝ} (E : Hyp w φ) {s0 : ℝ} (S : Sys (U w φ) (V φ) s0)
include E S

omit E in
/-- Inside a segment where λ keeps one sign of slope, `V − 2` cannot vanish (transversality). -/
theorem no_zero_inside {a b σ t : ℝ} (ha : a ∈ Ici s0) (ht : t ∈ Ioo a b)
    (hnn : ∀ t ∈ Ioo a b, 0 ≤ σ * (V φ t - 2)) (hσ : σ ^ 2 = 1) : V φ t ≠ 2 := by
  intro hV
  have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
  have tp := S.tpos ht0
  have hx := GTR.Sys.x_ne_of_zero S ht0 hV
  have hd : HasDerivAt (fun s => σ * (V φ s - 2)) (σ * (V φ t * (U w φ t - 1) / t)) t :=
    ((S.hV t ht0).sub_const 2).const_mul σ
  have hσ0 : σ ≠ 0 := by rintro h; rw [h] at hσ; norm_num at hσ
  have hd0 : σ * (V φ t * (U w φ t - 1) / t) ≠ 0 := by
    rw [hV]; exact mul_ne_zero hσ0 (div_ne_zero (mul_ne_zero two_ne_zero hx) tp.ne')
  have hval : σ * (V φ t - 2) = 0 := by rw [hV]; ring
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · obtain ⟨s, h1, h2⟩ := ((right_lt hd hneg).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hnn s ⟨ht.1.trans h2.1, h2.2⟩
    simp only [hval] at h1; linarith
  · obtain ⟨s, h1, h2⟩ := ((left_lt hd hpos).and (Ioo_mem_nhdsLT ht.1)).exists
    have := hnn s ⟨h2.1, h2.2.trans ht.2⟩
    simp only [hval] at h1; linarith

/-- On a segment where λ decreases, `V > 2` inside. -/
theorem pos_of_anti {a b : ℝ} (ha : a ∈ Ici s0) (hanti : StrictAntiOn (lam w) (Icc a b)) :
    ∀ t ∈ Ioo a b, 0 < (1 : ℝ) * (V φ t - 2) := by
  have hnn : ∀ t ∈ Ioo a b, 0 ≤ (1 : ℝ) * (V φ t - 2) := by
    intro t ht
    have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
    have tp := S.tpos ht0
    by_contra hc
    push Not at hc
    have hd := lam_deriv E tp
    have hpos : 0 < t * Real.exp (w t) * (2 + t * φ t) := by
      have : 2 + t * φ t = -(V φ t - 2) := by unfold V; ring
      rw [this]; apply mul_pos (by positivity); linarith
    obtain ⟨s, h1, h2⟩ := ((right_gt hd hpos).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hanti ⟨ht.1.le, ht.2.le⟩ ⟨(ht.1.trans h2.1).le, h2.2.le⟩ h2.1
    linarith
  intro t ht
  rcases (hnn t ht).lt_or_eq with h | h
  · exact h
  · exact absurd (by linarith : V φ t = 2) (no_zero_inside S ha ht hnn (by norm_num))

/-- On a segment where λ increases, `V < 2` inside. -/
theorem neg_of_mono {a b : ℝ} (ha : a ∈ Ici s0) (hmono : StrictMonoOn (lam w) (Icc a b)) :
    ∀ t ∈ Ioo a b, 0 < (-1 : ℝ) * (V φ t - 2) := by
  have hnn : ∀ t ∈ Ioo a b, 0 ≤ (-1 : ℝ) * (V φ t - 2) := by
    intro t ht
    have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
    have tp := S.tpos ht0
    by_contra hc
    push Not at hc
    have hd := lam_deriv E tp
    have hneg : t * Real.exp (w t) * (2 + t * φ t) < 0 := by
      have : 2 + t * φ t = -(V φ t - 2) := by unfold V; ring
      rw [this]; apply mul_neg_of_pos_of_neg (by positivity); linarith
    obtain ⟨s, h1, h2⟩ := ((right_lt hd hneg).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hmono ⟨ht.1.le, ht.2.le⟩ ⟨(ht.1.trans h2.1).le, h2.2.le⟩ h2.1
    linarith
  intro t ht
  rcases (hnn t ht).lt_or_eq with h | h
  · exact h
  · exact absurd (by linarith : V φ t = 2) (no_zero_inside S ha ht hnn (by norm_num))

end

/-- At a local extremum of λ at a positive radius, `V = 2`. -/
theorem V_two_of_extr {w φ : ℝ → ℝ} (E : Hyp w φ) {z : ℝ} (hz : 0 < z)
    (h : IsLocalMin (lam w) z ∨ IsLocalMax (lam w) z) : V φ z = 2 := by
  have hd := lam_deriv E hz
  have h0 : z * Real.exp (w z) * (2 + z * φ z) = 0 := by
    rcases h with h | h
    · exact h.hasDerivAt_eq_zero hd
    · exact h.hasDerivAt_eq_zero hd
  have : 2 + z * φ z = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  unfold V; linarith

theorem q_eq {xa xb Na Nb : ℝ} (hNa : Na = 8 * xa ^ 2) (hNb : Nb = 8 * xb ^ 2) (hs : xb * xa < 0) :
    xb / xa = -Real.exp ((Real.log Nb - Real.log Na) / 2) := by
  have ha : xa ≠ 0 := by rintro h; rw [h] at hs; simp at hs
  have hb : xb ≠ 0 := by rintro h; rw [h] at hs; simp at hs
  have hNa' : 0 < Na := by rw [hNa]; positivity
  have hNb' : 0 < Nb := by rw [hNb]; positivity
  have hq : xb / xa < 0 := by
    have : xb / xa = xb * xa / xa ^ 2 := by field_simp
    rw [this]; exact div_neg_of_neg_of_pos hs (by positivity)
  have e1 : Real.exp ((Real.log Nb - Real.log Na) / 2) ^ 2 = (xb / xa) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * ((Real.log Nb - Real.log Na) / 2) =
      Real.log Nb - Real.log Na by push_cast; ring, Real.exp_sub, Real.exp_log hNa', Real.exp_log hNb',
      hNa, hNb]
    field_simp
  have hp := Real.exp_pos ((Real.log Nb - Real.log Na) / 2)
  nlinarith [sq_nonneg (Real.exp ((Real.log Nb - Real.log Na) / 2) + xb / xa)]

end GTR
