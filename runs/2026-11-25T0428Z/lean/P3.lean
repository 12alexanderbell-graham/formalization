namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

/-- A function continuous on `[a, b]` with a nonnegative derivative inside does not decrease. -/
theorem le_of_deriv {G G' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn G (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt G (G' t) t) (hp : ∀ t ∈ Ioo a b, 0 ≤ G' t) : G a ≤ G b := by
  have hm : MonotoneOn G (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    · rw [interior_Icc]; exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht; rw [(hd t ht).deriv]; exact hp t ht
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem sigma_abs {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : 0 < σ * x) : |x| = σ * x := by
  have : |σ| = 1 := by
    have := sq_abs σ; rw [hσ] at this
    nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1), sq_nonneg (|σ| + 1)]
  rw [← abs_of_pos h, abs_mul, this, one_mul]

theorem fc_at_zero {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : 0 < σ * x) :
    σ * (4 * x + 0) / Real.sqrt (2 * Nw x 0) = 1 := by
  have e : 2 * Nw x 0 = (4 * |x|) ^ 2 := by unfold Nw; rw [mul_pow, sq_abs]; ring
  rw [e, Real.sqrt_sq (by positivity), sigma_abs hσ h]
  rw [div_eq_one_iff_eq (by positivity)]; ring

theorem fc_at_zero' {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : σ * x < 0) :
    σ * (4 * x + 0) / Real.sqrt (2 * Nw x 0) = -1 := by
  have h' : 0 < (-σ) * x := by linarith
  have := fc_at_zero (σ := -σ) (x := x) (by rw [neg_sq]; exact hσ) h'
  have e : σ * (4 * x + 0) / Real.sqrt (2 * Nw x 0) = -((-σ) * (4 * x + 0) / Real.sqrt (2 * Nw x 0)) := by
    ring
  rw [e, this]

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem N_le_of {a t : ℝ} (ha : a ∈ Ici s0) (hat : a ≤ t) :
    Nw (U t - 1) (V t - 2) ≤ Nw (U a - 1) (V a - 2) :=
  S.N_anti.antitoneOn ha (mem_Ici.2 (le_trans ha hat)) hat

theorem x_ne_of_zero {a : ℝ} (ha : a ∈ Ici s0) (hya : V a = 2) : U a - 1 ≠ 0 := by
  intro h
  have := S.N_pos ha
  rw [h, hya] at this; unfold Nw at this; norm_num at this

/-- At the left end of a segment on the side `σ`, `σ x > 0`. -/
theorem side_left {a b σ : ℝ} (ha : a ∈ Ici s0) (hab : a < b) (hya : V a = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : 0 < σ * (U a - 1) := by
  have ap := S.tpos ha
  have hd : HasDerivAt (fun t => σ * (V t - 2)) (σ * (V a * (U a - 1) / a)) a :=
    ((S.hV a ha).sub_const 2).const_mul σ
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | heq
  · have hneg : σ * (V a * (U a - 1) / a) < 0 := by
      rw [hya]
      have : σ * (2 * (U a - 1) / a) = 2 * (σ * (U a - 1)) / a := by ring
      rw [this]; exact div_neg_of_neg_of_pos (by linarith) ap
    have ev := Checked.Math.GelfandExtremaMain.right_lt hd hneg
    have ev2 : ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a b := Ioo_mem_nhdsGT hab
    obtain ⟨t, h1, h2⟩ := (ev.and ev2).exists
    have := hsg t h2
    simp only [hya, sub_self, mul_zero] at h1
    linarith
  · have hσ0 : σ ≠ 0 := by
      intro h0; obtain ⟨t, ht⟩ := nonempty_Ioo.2 hab; have := hsg t ht; rw [h0] at this; simp at this
    have := x_ne_of_zero S ha hya
    exact this (by rcases mul_eq_zero.1 heq with h | h; exact absurd h hσ0; exact h)

/-- At the right end of a segment on the side `σ`, `σ x < 0`. -/
theorem side_right {a b σ : ℝ} (ha : a ∈ Ici s0) (hab : a < b) (hyb : V b = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : σ * (U b - 1) < 0 := by
  have hb : b ∈ Ici s0 := mem_Ici.2 (le_trans ha hab.le)
  have bp := S.tpos hb
  have hd : HasDerivAt (fun t => σ * (V t - 2)) (σ * (V b * (U b - 1) / b)) b :=
    ((S.hV b hb).sub_const 2).const_mul σ
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | heq
  · have hpos : 0 < σ * (V b * (U b - 1) / b) := by
      rw [hyb]
      have : σ * (2 * (U b - 1) / b) = 2 * (σ * (U b - 1)) / b := by ring
      rw [this]; exact div_pos (by linarith) bp
    have ev := Checked.Math.GelfandExtremaMain.left_lt hd hpos
    have ev2 : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b := Ioo_mem_nhdsLT hab
    obtain ⟨t, h1, h2⟩ := (ev.and ev2).exists
    have := hsg t h2
    simp only [hyb, sub_self, mul_zero] at h1
    linarith
  · have hσ0 : σ ≠ 0 := by
      intro h0; obtain ⟨t, ht⟩ := nonempty_Ioo.2 hab; have := hsg t ht; rw [h0] at this; simp at this
    have := x_ne_of_zero S hb hyb
    exact this (by rcases mul_eq_zero.1 heq.symm with h | h; exact absurd h hσ0; exact h)

theorem th_left {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hya : V a = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : th σ U V a = 0 := by
  unfold th fc
  have h := fc_at_zero hσ (side_left S ha hab hya hsg)
  rw [hya, sub_self] at *
  rw [h, Real.arccos_one]

theorem th_right {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hyb : V b = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : th σ U V b = Real.pi := by
  unfold th fc
  have h := fc_at_zero' hσ (side_right S ha hab hyb hsg)
  rw [hyb, sub_self] at *
  rw [h, Real.arccos_neg_one]

end Sys
end GTR
