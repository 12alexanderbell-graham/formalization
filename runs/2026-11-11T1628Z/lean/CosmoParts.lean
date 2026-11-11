import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.CPLCoefficients
import Checked.Records.Findings
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Checked.Trust.NonVacuity
import Checked.Trust.Witnesses

open Set Filter Topology Checked.Cosmography Checked.Cosmography.Aviles

namespace Checked.Trust.NCF

/-! Generic redundancy of the parts `0 < a t` and `DifferentiableAt ℝ a t` of a flat expansion law. -/

theorem hubble_neg (a : ℝ → ℝ) (t : ℝ) : hubble (fun s => -a s) t = hubble a t := by
  simp only [hubble, deriv.fun_neg, neg_div_neg_eq]

theorem redshift_neg (a : ℝ → ℝ) (t₀ t : ℝ) : redshift (fun s => -a s) t₀ t = redshift a t₀ t := by
  simp only [redshift, neg_div_neg_eq]

theorem decel_neg (a : ℝ → ℝ) (t : ℝ) : decel (fun s => -a s) t = decel a t := by
  have h1 : deriv (fun s => -a s) = fun s => -deriv a s := funext fun s => deriv.fun_neg
  simp only [decel, h1, deriv.fun_neg]
  ring

theorem cosmoCoeff_neg (n : ℕ) (a : ℝ → ℝ) (t : ℝ) :
    cosmoCoeff n (fun s => -a s) t = cosmoCoeff n a t := by
  simp only [cosmoCoeff, iteratedDeriv_fun_neg, hubble_neg]
  rw [neg_mul, neg_div_neg_eq]

/-- A law `H(t) = H(t₀) g(z(t))` with `g` continuous at `0`, `g 0 = 1`, and `H(t₀) > 0` makes `a`
differentiable near `t₀` (a junk derivative 0 would give `H = 0` where `g > 0`). -/
theorem eventually_diff_of_law {a : ℝ → ℝ} {t₀ : ℝ} {g : ℝ → ℝ} (hg : ContinuousAt g 0) (hg0 : g 0 = 1)
    (hH : 0 < hubble a t₀) (hlaw : ∀ᶠ t in 𝓝 t₀, hubble a t = hubble a t₀ * g (redshift a t₀ t)) :
    ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t := by
  have hd0 : deriv a t₀ ≠ 0 := by
    intro h; simp [hubble, h] at hH
  have ha0 : a t₀ ≠ 0 := by
    intro h; simp [hubble, h] at hH
  have hdiff : DifferentiableAt ℝ a t₀ := by
    by_contra hn; exact hd0 (deriv_zero_of_not_differentiableAt hn)
  have hz : Tendsto (fun t => redshift a t₀ t) (𝓝 t₀) (𝓝 0) := by
    have : Tendsto (fun t => a t₀ / a t - 1) (𝓝 t₀) (𝓝 (a t₀ / a t₀ - 1)) :=
      ((tendsto_const_nhds.div hdiff.continuousAt.tendsto ha0).sub tendsto_const_nhds)
    simpa [redshift, div_self ha0] using this
  have hgpos : ∀ᶠ t in 𝓝 t₀, 0 < g (redshift a t₀ t) := by
    have : Tendsto (fun t => g (redshift a t₀ t)) (𝓝 t₀) (𝓝 1) := by
      rw [← hg0]; exact hg.tendsto.comp hz
    exact this.eventually (lt_mem_nhds one_pos)
  filter_upwards [hlaw, hgpos] with t ht hp
  by_contra hn
  have : hubble a t = 0 := by simp [hubble, deriv_zero_of_not_differentiableAt hn]
  rw [this] at ht
  have : 0 < hubble a t₀ * g (redshift a t₀ t) := mul_pos hH hp
  linarith

/-- With `H(t₀) > 0` and `a` differentiable near `t₀`, either `a > 0` near `t₀` or `-a > 0` near `t₀`. -/
theorem eventually_sign {a : ℝ → ℝ} {t₀ : ℝ} (hH : 0 < hubble a t₀)
    (hd : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t) :
    (∀ᶠ t in 𝓝 t₀, 0 < a t) ∨ (∀ᶠ t in 𝓝 t₀, 0 < -a t) := by
  have ha0 : a t₀ ≠ 0 := by
    intro h; simp [hubble, h] at hH
  have hc : ContinuousAt a t₀ := hd.self_of_nhds.continuousAt
  rcases lt_or_gt_of_ne ha0 with h | h
  · right; exact hc.eventually (gt_mem_nhds h) |>.mono fun t ht => by linarith
  · left; exact hc.eventually (lt_mem_nhds h)


/-- The flat ΛCDM law with the part `0 < a t` dropped holds for `a` or for `-a`. -/
theorem lcdm_noPos {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)) :
    IsFlatLCDM Ω a t₀ ∨ IsFlatLCDM Ω (fun s => -a s) t₀ := by
  obtain ⟨hH, hev⟩ := h
  rcases eventually_sign hH (hev.mono fun t h => h.1) with hp | hn
  · exact Or.inl ⟨hH, (hp.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  · refine Or.inr ⟨by rwa [hubble_neg], (hn.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2.neg, ?_⟩⟩
    rw [hubble_neg, hubble_neg, redshift_neg]; exact h3

/-- The flat ΛCDM law with the part `DifferentiableAt ℝ a t` dropped still holds. -/
theorem lcdm_noDiff {Ω : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 + 1 - Ω)) :
    IsFlatLCDM Ω a t₀ := by
  obtain ⟨hH, hev⟩ := h
  have hd := eventually_diff_of_law (g := fun z => √(Ω * (1 + z) ^ 3 + 1 - Ω)) (by fun_prop)
    (by norm_num) hH (hev.mono fun t h => h.2)
  exact ⟨hH, (hev.and hd).mono fun t ⟨⟨h1, h3⟩, h2⟩ => ⟨h1, h2, h3⟩⟩

/-- The same for flat CPL, part `0 < a t` dropped. -/
theorem cpl_noPos {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 +
      (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) *
        Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))) :
    CPL.IsFlatCPL Ω w₀ wₐ a t₀ ∨ CPL.IsFlatCPL Ω w₀ wₐ (fun s => -a s) t₀ := by
  obtain ⟨hH, hev⟩ := h
  rcases eventually_sign hH (hev.mono fun t h => h.1) with hp | hn
  · exact Or.inl ⟨hH, (hp.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  · refine Or.inr ⟨by rwa [hubble_neg], (hn.and hev).mono fun t ⟨h1, h2, h3⟩ => ⟨h1, h2.neg, ?_⟩⟩
    rw [hubble_neg, hubble_neg, redshift_neg]; exact h3

/-- The same for flat CPL, part `DifferentiableAt ℝ a t` dropped. -/
theorem cpl_noDiff {Ω w₀ wₐ : ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (h : 0 < hubble a t₀ ∧ ∀ᶠ t in 𝓝 t₀, 0 < a t ∧
      hubble a t = hubble a t₀ * √(Ω * (1 + redshift a t₀ t) ^ 3 +
      (1 - Ω) * (1 + redshift a t₀ t) ^ (3 * (1 + w₀ + wₐ)) *
        Real.exp (-(3 * wₐ * redshift a t₀ t) / (1 + redshift a t₀ t)))) :
    CPL.IsFlatCPL Ω w₀ wₐ a t₀ := by
  obtain ⟨hH, hev⟩ := h
  have hg : ContinuousAt (fun z : ℝ => √(Ω * (1 + z) ^ 3 + (1 - Ω) * (1 + z) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * z) / (1 + z)))) 0 := by
    have h1 : ContinuousAt (fun z : ℝ => (1 + z) ^ (3 * (1 + w₀ + wₐ))) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
    have h2 : ContinuousAt (fun z : ℝ => -(3 * wₐ * z) / (1 + z)) 0 :=
      (continuousAt_const.mul continuousAt_id).neg.div (continuousAt_const.add continuousAt_id)
        (by norm_num)
    exact ((continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 3)).add
      ((continuousAt_const.mul h1).mul (Real.continuous_exp.continuousAt.comp h2))).sqrt
  have hd := eventually_diff_of_law hg (by norm_num) hH (hev.mono fun t h => h.2)
  exact ⟨hH, (hev.and hd).mono fun t ⟨⟨h1, h3⟩, h2⟩ => ⟨h1, h2, h3⟩⟩

/-! Witnesses (parts semantics: parts of `IsFlatLCDM`/`IsFlatCPL` are 1 `0 < H₀`, 2 `0 < a t`,
3 `DifferentiableAt ℝ a t`, 4 the law). -/

theorem flatLCDM_coeffs_p1_2 : dropped% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 2 := by
  intro Ω a t₀ hs h
  rcases lcdm_noPos h with hL | hL
  · exact flatLCDM_coeffs Ω a t₀ hL hs
  · simpa only [decel_neg, cosmoCoeff_neg] using flatLCDM_coeffs Ω _ t₀ hL hs.neg

theorem flatLCDM_coeffs_p1_3 : dropped% Checked.Cosmography.Aviles.flatLCDM_coeffs 1 3 := by
  intro Ω a t₀ hs h
  exact flatLCDM_coeffs Ω a t₀ (lcdm_noDiff h) hs

theorem flatCPL_coeffs_p1_2 : dropped% Checked.Cosmography.CPL.flatCPL_coeffs 1 2 := by
  intro Ω w₀ wₐ a t₀ hs h
  rcases cpl_noPos h with hL | hL
  · exact CPL.flatCPL_coeffs Ω w₀ wₐ a t₀ hL hs
  · simpa only [decel_neg, cosmoCoeff_neg] using CPL.flatCPL_coeffs Ω w₀ wₐ _ t₀ hL hs.neg

theorem flatCPL_coeffs_p1_3 : dropped% Checked.Cosmography.CPL.flatCPL_coeffs 1 3 := by
  intro Ω w₀ wₐ a t₀ hs h
  exact CPL.flatCPL_coeffs Ω w₀ wₐ a t₀ (cpl_noDiff h) hs

end Checked.Trust.NCF
