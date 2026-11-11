import Mathlib

open Set Filter Topology

namespace Scratch.JunkCrit

noncomputable def cubicP (R a b u w T v : ℝ) : ℝ := R * T / (v - b) - a / (v ^ 2 + u * b * v + w * b ^ 2)
def IsCriticalIsotherm (p : ℝ → ℝ) (v : ℝ) : Prop := deriv p v = 0 ∧ deriv (deriv p) v = 0

/-- A function that is differentiable just to the right of `v₀` and unbounded there satisfies the
critical-point condition at `v₀` in Lean's total calculus: it is not differentiable at `v₀`, and its
derivative is not differentiable at `v₀` either, so both junk derivatives are 0. -/
theorem crit_of_unbounded (p : ℝ → ℝ) (v₀ : ℝ)
    (hd : ∀ᶠ x in 𝓝[>] v₀, DifferentiableAt ℝ p x)
    (hu : Tendsto (fun x => |p x|) (𝓝[>] v₀) atTop) : IsCriticalIsotherm p v₀ := by
  -- no bound on any right neighbourhood
  have nobound : ∀ M δ : ℝ, 0 < δ → ∃ x ∈ Ioo v₀ (v₀ + δ), M < |p x| := by
    intro M δ hδ
    have h1 : ∀ᶠ x in 𝓝[>] v₀, M < |p x| := hu.eventually_gt_atTop M
    have h2 : ∀ᶠ x in 𝓝[>] v₀, x ∈ Ioo v₀ (v₀ + δ) := Ioo_mem_nhdsGT (by linarith)
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    exact ⟨x, hx2, hx1⟩
  constructor
  · by_cases h : DifferentiableAt ℝ p v₀
    · exfalso
      have hc : Tendsto (fun x => |p x|) (𝓝[>] v₀) (𝓝 (|p v₀|)) :=
        ((h.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).abs
      exact not_tendsto_nhds_of_tendsto_atTop hu _ hc
    · exact deriv_zero_of_not_differentiableAt h
  · by_cases h : DifferentiableAt ℝ (deriv p) v₀
    · exfalso
      have hc := h.continuousAt
      have hev : ∀ᶠ x in 𝓝[>] v₀, |deriv p x| ≤ |deriv p v₀| + 1 ∧ DifferentiableAt ℝ p x := by
        refine Filter.Eventually.and ?_ hd
        have : ∀ᶠ x in 𝓝 v₀, |deriv p x - deriv p v₀| < 1 := by
          have := Metric.tendsto_nhds.1 hc 1 one_pos
          simpa [Real.dist_eq] using this
        refine (this.filter_mono nhdsWithin_le_nhds).mono fun x hx => ?_
        have := abs_sub_abs_le_abs_sub (deriv p x) (deriv p v₀)
        linarith
      obtain ⟨u, hu', hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
      set M := |deriv p v₀| + 1
      set x₁ := (v₀ + u) / 2
      have hx₁ : x₁ ∈ Ioo v₀ u := ⟨by simp only [x₁]; linarith [hu'.out], by simp only [x₁]; linarith [hu'.out]⟩
      have hbound : ∀ x ∈ Ioo v₀ x₁, |p x| ≤ |p x₁| + M * (u - v₀) := by
        intro x hx
        have hs : Icc x x₁ ⊆ Ioo v₀ u := fun y hy => ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hx₁.2⟩
        have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := p) (C := M) (s := Icc x x₁)
          (fun y hy => (hsub (hs hy)).2) (fun y hy => by rw [Real.norm_eq_abs]; exact (hsub (hs hy)).1)
          (convex_Icc x x₁) ⟨le_rfl, hx.2.le⟩ ⟨hx.2.le, le_rfl⟩
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ x₁ - x by linarith [hx.2])] at h
        have hM : 0 ≤ M := by positivity
        have : M * (x₁ - x) ≤ M * (u - v₀) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.1, hx₁.2]) hM
        have := abs_sub_abs_le_abs_sub (p x) (p x₁)
        rw [abs_sub_comm] at h
        linarith
      obtain ⟨x, hx, hxM⟩ := nobound (|p x₁| + M * (u - v₀)) (x₁ - v₀) (by linarith [hx₁.1])
      have : x ∈ Ioo v₀ x₁ := ⟨hx.1, by linarith [hx.2]⟩
      linarith [hbound x this]
    · exact deriv_zero_of_not_differentiableAt h


/-- `|h + k / g|` tends to infinity just to the right of a zero of `g` (with `h`, `g` continuous there
and `g` nonzero just to the right). -/
theorem abs_add_div_tendsto (h g : ℝ → ℝ) (k v₀ : ℝ) (hk : k ≠ 0) (hh : ContinuousAt h v₀)
    (hg : ContinuousAt g v₀) (hg0 : g v₀ = 0) (hne : ∀ᶠ x in 𝓝[>] v₀, g x ≠ 0) :
    Tendsto (fun x => |h x + k / g x|) (𝓝[>] v₀) atTop := by
  have hg' : Tendsto (fun x => |g x|) (𝓝[>] v₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hne.mono fun x hx => abs_pos.2 hx⟩
    have := ((hg.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi v₀))).abs :
      Tendsto (fun x => |g x|) (𝓝[>] v₀) (𝓝 |g v₀|))
    simpa [hg0] using this
  have hinv : Tendsto (fun x => |k| * |g x|⁻¹) (𝓝[>] v₀) atTop :=
    (tendsto_inv_nhdsGT_zero.comp hg').const_mul_atTop (abs_pos.2 hk)
  have hb : ∀ᶠ x in 𝓝[>] v₀, |h x| ≤ |h v₀| + 1 := by
    have : ∀ᶠ x in 𝓝 v₀, |h x - h v₀| < 1 := by
      have := Metric.tendsto_nhds.1 hh.tendsto 1 one_pos
      simpa [Real.dist_eq] using this
    refine (this.filter_mono nhdsWithin_le_nhds).mono fun x hx => ?_
    have := abs_sub_abs_le_abs_sub (h x) (h v₀)
    linarith
  have h2 : Tendsto (fun x => |k| * |g x|⁻¹ - (|h v₀| + 1)) (𝓝[>] v₀) atTop :=
    tendsto_atTop_add_const_right _ _ hinv
  refine tendsto_atTop_mono' _ (hb.mono fun x hx => ?_) h2
  have e : |k / g x| = |k| * |g x|⁻¹ := by rw [abs_div, div_eq_mul_inv]
  have := abs_sub_abs_le_abs_sub (k / g x) (-h x)
  rw [sub_neg_eq_add, add_comm] at this
  rw [abs_neg] at this
  linarith

/-- The denominator of the cubic isotherm. -/
theorem cubicP_eq (R a b u w T x : ℝ) : cubicP R a b u w T x =
    R * T / (x - b) + (-a) / (x ^ 2 + u * b * x + w * b ^ 2) := by
  unfold cubicP; rw [neg_div]; ring

theorem cubicP_diff (R a b u w T x : ℝ) (hx : x - b ≠ 0) (hD : x ^ 2 + u * b * x + w * b ^ 2 ≠ 0) :
    DifferentiableAt ℝ (cubicP R a b u w T) x := by
  unfold cubicP
  apply DifferentiableAt.sub
  · exact (differentiableAt_const _).div (differentiableAt_id.sub_const _) hx
  · exact (differentiableAt_const _).div (by fun_prop) hD

/-- At the co-volume `v = b` (where `R T / (v − b)` has its pole) the cubic isotherm meets the
critical-point condition by the junk derivatives, whenever `R T ≠ 0` and the attraction denominator is
nonzero at `b`. -/
theorem crit_at_b (R a b u w T : ℝ) (hRT : R * T ≠ 0) (hD : b ^ 2 + u * b * b + w * b ^ 2 ≠ 0) :
    IsCriticalIsotherm (cubicP R a b u w T) b := by
  have hDc : ContinuousAt (fun x => x ^ 2 + u * b * x + w * b ^ 2) b := by fun_prop
  have hDne : ∀ᶠ x in 𝓝 b, x ^ 2 + u * b * x + w * b ^ 2 ≠ 0 := hDc.eventually_ne hD
  apply crit_of_unbounded
  · filter_upwards [hDne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hxb
    exact cubicP_diff R a b u w T x (sub_ne_zero.2 (ne_of_gt hxb)) hx
  · have := abs_add_div_tendsto (fun x => (-a) / (x ^ 2 + u * b * x + w * b ^ 2)) (fun x => x - b)
      (R * T) b hRT (continuousAt_const.div hDc hD) (by fun_prop) (by simp)
      (Filter.mem_of_superset (self_mem_nhdsWithin (s := Ioi b)) fun x (hx : b < x) =>
        sub_ne_zero.2 (ne_of_gt hx))
    refine this.congr fun x => ?_
    rw [cubicP_eq]; ring_nf

/-- At a zero `v₀ > b` of the attraction denominator the cubic isotherm (with `a ≠ 0`) meets the
critical-point condition by the junk derivatives. -/
theorem crit_at_root (R a b u w T v₀ : ℝ) (hb : b < v₀) (ha : a ≠ 0)
    (hD : v₀ ^ 2 + u * b * v₀ + w * b ^ 2 = 0)
    (hne : ∀ᶠ x in 𝓝[>] v₀, x ^ 2 + u * b * x + w * b ^ 2 ≠ 0) :
    IsCriticalIsotherm (cubicP R a b u w T) v₀ := by
  apply crit_of_unbounded
  · filter_upwards [hne, self_mem_nhdsWithin] with x hx hxv
    exact cubicP_diff R a b u w T x (sub_ne_zero.2 (ne_of_gt (hb.trans hxv))) hx
  · have := abs_add_div_tendsto (fun x => R * T / (x - b)) (fun x => x ^ 2 + u * b * x + w * b ^ 2)
      (-a) v₀ (neg_ne_zero.2 ha)
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 (ne_of_gt hb)))
      (by fun_prop) hD hne
    exact this.congr fun x => by rw [cubicP_eq]

end Scratch.JunkCrit
