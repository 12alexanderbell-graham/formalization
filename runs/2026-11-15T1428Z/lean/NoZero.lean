import Checked.Trust.NecessityAP

open Set Filter Topology Asymptotics MeasureTheory
open Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.B1

namespace Checked.Trust.NCAP

/-- A scale factor positive at the observation time, differentiable on the interval, with
`deriv a · √a ≥ c > 0` wherever it is positive, has no zero on the interval: just after its last zero the
derivative would grow without bound (`deriv a = c/√a`), against differentiability at that zero. -/
theorem no_zero_core (a : ℝ → ℝ) (t t₀ c : ℝ) (hc : 0 < c) (htt : t ≤ t₀)
    (hdiff : ∀ s ∈ Icc t t₀, DifferentiableAt ℝ a s) (ha₀ : 0 < a t₀)
    (hd : ∀ s ∈ Icc t t₀, 0 < a s → c ≤ deriv a s * √(a s)) : ∀ s ∈ Icc t t₀, 0 < a s := by
  have hcont : ContinuousOn a (Icc t t₀) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  by_contra hneg
  push Not at hneg
  obtain ⟨s, hs, hs0⟩ := hneg
  -- the set of zeros in [s, t₀]
  set Z := {x ∈ Icc s t₀ | a x = 0} with hZ
  have hsub : Icc s t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left hs.1
  have hZne : Z.Nonempty := by
    obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hs.2 (hcont.mono hsub) ⟨hs0, ha₀.le⟩
    exact ⟨x, hx, hx0⟩
  have hZc : IsClosed Z := (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc
    isClosed_singleton
  have hZb : BddAbove Z := ⟨t₀, fun x hx => hx.1.2⟩
  have hZcpt : IsCompact Z := Metric.isCompact_of_isClosed_isBounded hZc
    (Metric.isBounded_Icc s t₀ |>.subset (fun x hx => hx.1))
  set s₁ := sSup Z with hs₁
  have hs₁Z : s₁ ∈ Z := hZcpt.sSup_mem hZne
  have hs₁0 : a s₁ = 0 := hs₁Z.2
  have hs₁t : s₁ ∈ Icc t t₀ := hsub hs₁Z.1
  have hlt : s₁ < t₀ := lt_of_le_of_ne hs₁Z.1.2 (fun h => by rw [h] at hs₁0; linarith)
  -- positivity after s₁
  have hposR : ∀ x ∈ Ioc s₁ t₀, 0 < a x := by
    intro x hx
    by_contra hx0
    push Not at hx0
    have hsx : Icc x t₀ ⊆ Icc t t₀ := Icc_subset_Icc_left (le_trans hs₁t.1 hx.1.le)
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hx.2 (hcont.mono hsx) ⟨hx0, ha₀.le⟩
    have hyZ : y ∈ Z := ⟨⟨le_trans hs₁Z.1.1 (hx.1.le.trans hy.1), hy.2⟩, hy0⟩
    have := le_csSup hZb hyZ
    linarith [hx.1, hy.1]
  -- the derivative estimate at s₁
  obtain ⟨D, hD⟩ : ∃ D, HasDerivAt a D s₁ := ⟨_, (hdiff s₁ hs₁t).hasDerivAt⟩
  have hlo := hD.isLittleO
  have hev := hlo.def (by norm_num : (0 : ℝ) < 1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set M := max (D + 1) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hup : ∀ x, s₁ < x → x < s₁ + δ → a x ≤ M * (x - s₁) := by
    intro x h1 h2
    have hx := hball (show dist x s₁ < δ by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    rw [hs₁0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_of_pos (by linarith : 0 < x - s₁)] at hx
    have := (abs_le.1 hx).2
    have : D + 1 ≤ M := le_max_left _ _
    nlinarith
  -- pick y small
  set y := min (δ / 2) (min ((t₀ - s₁) / 2) (c ^ 2 / (2 * M ^ 3))) with hy
  have hy0 : 0 < y := lt_min (by linarith) (lt_min (by linarith) (by positivity))
  have hyδ : y < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hyt : s₁ + y ≤ t₀ := by
    have : y ≤ (t₀ - s₁) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hyc : y < c ^ 2 / M ^ 3 := by
    have h1 : y ≤ c ^ 2 / (2 * M ^ 3) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h2 : c ^ 2 / (2 * M ^ 3) < c ^ 2 / M ^ 3 :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (by nlinarith [pow_pos (by linarith : (0:ℝ) < M) 3])
    linarith
  -- mean value theorem on [s₁, s₁ + y]
  set x := s₁ + y
  have hxt : Icc s₁ x ⊆ Icc t t₀ := fun z hz => ⟨le_trans hs₁t.1 hz.1, le_trans hz.2 hyt⟩
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope a (deriv a) (by linarith : s₁ < x)
    (hcont.mono hxt) (fun z hz => (hdiff z (hxt (Ioo_subset_Icc_self hz))).hasDerivAt)
  have hξpos : 0 < a ξ := hposR ξ ⟨hξ.1, le_trans hξ.2.le hyt⟩
  have hxpos : 0 < a x := hposR x ⟨by linarith, hyt⟩
  have hξup : a ξ ≤ M * (ξ - s₁) := hup ξ hξ.1 (by linarith [hξ.2])
  have hxup : a x ≤ M * (x - s₁) := hup x (by linarith) (by linarith)
  have hdξ := hd ξ (hxt (Ioo_subset_Icc_self hξ)) hξpos
  rw [hξd, hs₁0, sub_zero] at hdξ
  have hxs : x - s₁ = y := by ring
  rw [hxs] at hdξ hxup
  -- c ≤ (a x / y) √(a ξ) ≤ M √(a ξ), so c² ≤ M² a ξ ≤ M³ y
  have hsq : √(a ξ) ^ 2 = a ξ := Real.sq_sqrt hξpos.le
  have hsn : 0 ≤ √(a ξ) := Real.sqrt_nonneg _
  have h1 : a x / y ≤ M := by rw [div_le_iff₀ hy0]; linarith
  have h2 : c ≤ M * √(a ξ) := le_trans hdξ (mul_le_mul_of_nonneg_right h1 hsn)
  have h3 : c ^ 2 ≤ M ^ 2 * a ξ := by nlinarith
  have h4 : a ξ ≤ M * y := le_trans hξup (by nlinarith [hξ.2])
  have h5 : c ^ 2 ≤ M ^ 3 * y := by nlinarith
  have h6 : M ^ 3 * y < c ^ 2 := by
    rw [lt_div_iff₀ (by positivity)] at hyc; linarith
  linarith

end Checked.Trust.NCAP
