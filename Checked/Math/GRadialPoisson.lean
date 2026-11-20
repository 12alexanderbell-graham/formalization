import Checked.Math.RadialLaplacian
import Checked.Math.RadialC2
import Checked.Math.GelfandPDEExists
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Radial Poisson problem in the unit ball of ℝ³ with zero boundary values: the explicit radial
solution operator `P`, and its lift to a C² function on the ball with Mathlib's Laplacian. Promoted from `Work/Math/GRadialPoisson.lean`.
-/

namespace Checked.Math.GRadialPoisson
open Set Filter Topology InnerProductSpace Laplacian Metric
open scoped Interval

/-- The radial Dirichlet solution operator in the unit ball of ℝ³: for a source profile h,
P h r = (1/r − 1) ∫₀^r t² h(t) dt + ∫_r^1 (t − t²) h(t) dt  (for r > 0; at r = 0 the first term is read as 0). -/
noncomputable def P (h : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r⁻¹ - 1) * (∫ t in (0:ℝ)..r, t ^ 2 * h t) + ∫ t in r..1, (t - t ^ 2) * h t

theorem grp_hasDerivAt_I {h : ℝ → ℝ} (hc : Continuous h) (r : ℝ) :
    HasDerivAt (fun r => ∫ t in (0:ℝ)..r, t ^ 2 * h t) (r ^ 2 * h r) r :=
  (((continuous_pow 2).mul hc).integral_hasStrictDerivAt 0 r).hasDerivAt

theorem grp_hasDerivAt_J {h : ℝ → ℝ} (hc : Continuous h) (r : ℝ) :
    HasDerivAt (fun r => ∫ t in r..1, (t - t ^ 2) * h t) (-((r - r ^ 2) * h r)) r := by
  have e : (fun r => ∫ t in r..1, (t - t ^ 2) * h t) =
      fun r => -∫ t in (1:ℝ)..r, (t - t ^ 2) * h t := by
    funext r; exact intervalIntegral.integral_symm _ _
  rw [e]
  exact ((((continuous_id.sub (continuous_pow 2)).mul hc).integral_hasStrictDerivAt 1 r).hasDerivAt).neg

theorem grp_hasDerivAt_P {h : ℝ → ℝ} (hc : Continuous h) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (P h) (-(∫ t in (0:ℝ)..r, t ^ 2 * h t) / r ^ 2) r := by
  have e : P h = fun r => (r⁻¹ - 1) * (∫ t in (0:ℝ)..r, t ^ 2 * h t) +
      ∫ t in r..1, (t - t ^ 2) * h t := rfl
  rw [e]
  have d := (((hasDerivAt_inv hr).sub_const 1).mul (grp_hasDerivAt_I hc r)).add
    (grp_hasDerivAt_J hc r)
  convert d using 1
  field_simp
  ring

theorem grp_hasDerivAt_F1 {h : ℝ → ℝ} (hc : Continuous h) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r => -(∫ t in (0:ℝ)..r, t ^ 2 * h t) / r ^ 2)
      (-h r + 2 * (∫ t in (0:ℝ)..r, t ^ 2 * h t) / r ^ 3) r := by
  have d := (grp_hasDerivAt_I hc r).neg.div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr)
  convert d using 1
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- `P h r - P h 0` as a single integral. -/
theorem grp_diff {h : ℝ → ℝ} (hc : Continuous h) {r : ℝ} (_hr : 0 < r) :
    P h r - P h 0 = ∫ t in (0:ℝ)..r, (t ^ 2 * r⁻¹ - t) * h t := by
  have ii : ∀ (g : ℝ → ℝ), Continuous g → ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
    fun g hg a b => hg.intervalIntegrable a b
  have c1 : Continuous fun t : ℝ => t ^ 2 * h t := (continuous_pow 2).mul hc
  have c2 : Continuous fun t : ℝ => (t - t ^ 2) * h t := (continuous_id.sub (continuous_pow 2)).mul hc
  have hP0 : P h 0 = ∫ t in (0:ℝ)..1, (t - t ^ 2) * h t := by simp [P]
  rw [hP0, ← intervalIntegral.integral_add_adjacent_intervals (ii _ c2 0 r) (ii _ c2 r 1)]
  unfold P
  have : (r⁻¹ - 1) * (∫ t in (0:ℝ)..r, t ^ 2 * h t) - ∫ t in (0:ℝ)..r, (t - t ^ 2) * h t =
      ∫ t in (0:ℝ)..r, (t ^ 2 * r⁻¹ - t) * h t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((ii _ c1 0 r).const_mul _) (ii _ c2 0 r)]
    congr 1; funext t; ring
  linarith

theorem grp_C_nonneg {h : ℝ → ℝ} {C : ℝ} (hlip : ∀ t ∈ Icc (0:ℝ) 1, |h t - h 0| ≤ C * t) :
    0 ≤ C := by
  have := hlip 1 ⟨zero_le_one, le_rfl⟩
  linarith [abs_nonneg (h 1 - h 0)]

theorem grp_quad {h : ℝ → ℝ} {C : ℝ} (hc : Continuous h)
    (hlip : ∀ t ∈ Icc (0:ℝ) 1, |h t - h 0| ≤ C * t) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    |P h r - P h 0| ≤ (|h 0| + C) * r ^ 2 := by
  rcases eq_or_lt_of_le hr.1 with h0 | hr0
  · subst h0; simp
  rw [grp_diff hc hr0]
  have hC := grp_C_nonneg hlip
  have b : ∀ t ∈ Ι (0:ℝ) r, ‖(t ^ 2 * r⁻¹ - t) * h t‖ ≤ r * (|h 0| + C) := by
    intro t ht
    rw [uIoc_of_le hr0.le] at ht
    have ht1 : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.trans hr.2⟩
    have hb : |h t| ≤ |h 0| + C := by
      have := hlip t ht1
      have : |h t| ≤ |h t - h 0| + |h 0| := by
        calc |h t| = |(h t - h 0) + h 0| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      nlinarith [ht1.2]
    have q1 : t ^ 2 * r⁻¹ ≤ t := by
      rw [← div_eq_mul_inv, div_le_iff₀ hr0]; nlinarith [ht.1, ht.2]
    have q2 : 0 ≤ t ^ 2 * r⁻¹ := by positivity
    have ha : |t ^ 2 * r⁻¹ - t| ≤ r := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hr0.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const b
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hr0] at this
  calc _ ≤ r * (|h 0| + C) * r := this
    _ = _ := by ring

theorem grp_I_est {h : ℝ → ℝ} {C : ℝ} (hc : Continuous h)
    (hlip : ∀ t ∈ Icc (0:ℝ) 1, |h t - h 0| ≤ C * t) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    |(∫ t in (0:ℝ)..r, t ^ 2 * h t) - h 0 * r ^ 3 / 3| ≤ C * r ^ 4 := by
  have hC := grp_C_nonneg hlip
  have e : (∫ t in (0:ℝ)..r, t ^ 2 * h t) - h 0 * r ^ 3 / 3 =
      ∫ t in (0:ℝ)..r, t ^ 2 * (h t - h 0) := by
    have i2 : (∫ t in (0:ℝ)..r, t ^ 2 * h 0) = h 0 * r ^ 3 / 3 := by
      rw [intervalIntegral.integral_mul_const, integral_pow]; ring
    have c1 : Continuous fun t : ℝ => t ^ 2 * h t := (continuous_pow 2).mul hc
    have c0 : Continuous fun t : ℝ => t ^ 2 * h 0 := (continuous_pow 2).mul continuous_const
    rw [← i2, ← intervalIntegral.integral_sub (c1.intervalIntegrable 0 r) (c0.intervalIntegrable 0 r)]
    congr 1; funext t; ring
  rw [e]
  have b : ∀ t ∈ Ι (0:ℝ) r, ‖t ^ 2 * (h t - h 0)‖ ≤ r ^ 2 * (C * r) := by
    intro t ht
    rw [uIoc_of_le hr0.le] at ht
    have := hlip t ⟨ht.1.le, ht.2.trans hr1⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t)]
    apply mul_le_mul _ _ (abs_nonneg _) (sq_nonneg r)
    · exact pow_le_pow_left₀ ht.1.le ht.2 2
    · nlinarith [ht.2]
  have := intervalIntegral.norm_integral_le_of_norm_le_const b
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hr0] at this
  calc _ ≤ r ^ 2 * (C * r) * r := this
    _ = _ := by ring

theorem grp_continuousOn {h : ℝ → ℝ} {C : ℝ} (hc : Continuous h)
    (hlip : ∀ t ∈ Icc (0:ℝ) 1, |h t - h 0| ≤ C * t) : ContinuousOn (P h) (Icc 0 1) := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with h0 | hr0
  · subst h0
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun r : ℝ => (|h 0| + C) * r ^ 2) (𝓝[Icc 0 1] 0) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => (|h 0| + C) * r ^ 2) (𝓝 0) (𝓝 ((|h 0| + C) * 0 ^ 2)) :=
        ((continuous_const.mul (continuous_pow 2)).tendsto 0)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Real.norm_eq_abs]
    exact grp_quad hc hlip hs
  · exact (grp_hasDerivAt_P hc hr0.ne').continuousAt.continuousWithinAt

theorem lift (h : ℝ → ℝ) (C : ℝ) (hc : Continuous h)
    (hlip : ∀ t ∈ Set.Icc (0:ℝ) 1, |h t - h 0| ≤ C * t) :
    ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => P h ‖x‖) (Metric.ball 0 1) ∧
    ContinuousOn (fun x : EuclideanSpace ℝ (Fin 3) => P h ‖x‖) (Metric.closedBall 0 1) ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → P h ‖x‖ = 0) ∧
    (∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Δ (fun y : EuclideanSpace ℝ (Fin 3) => P h ‖y‖) x = - h ‖x‖) := by
  have hC := grp_C_nonneg hlip
  set I : ℝ → ℝ := fun r => ∫ t in (0:ℝ)..r, t ^ 2 * h t with hI
  set F1 : ℝ → ℝ := fun r => -(∫ t in (0:ℝ)..r, t ^ 2 * h t) / r ^ 2 with hF1d
  set F2 : ℝ → ℝ := fun r => -h r + 2 * (∫ t in (0:ℝ)..r, t ^ 2 * h t) / r ^ 3 with hF2d
  have hF1 : ∀ ρ ∈ Ioo (0:ℝ) 1, HasDerivAt (P h) (F1 ρ) ρ := fun ρ hρ =>
    grp_hasDerivAt_P hc hρ.1.ne'
  have hF2 : ∀ ρ ∈ Ioo (0:ℝ) 1, HasDerivAt F1 (F2 ρ) ρ := fun ρ hρ =>
    grp_hasDerivAt_F1 hc hρ.1.ne'
  have hF2c : ContinuousOn F2 (Ioo 0 1) := by
    intro ρ hρ
    have cI : ContinuousAt I ρ := (grp_hasDerivAt_I hc ρ).continuousAt
    exact (hc.continuousAt.neg.add ((continuousAt_const.mul cI).div
      (continuousAt_id.pow 3) (pow_ne_zero 3 hρ.1.ne'))).continuousWithinAt
  set L : ℝ := -(h 0 / 3) with hL
  set C' : ℝ := 4 * C + |h 0| with hC'
  have hM : ∀ ρ ∈ Ioo (0:ℝ) 1, |F1 ρ / ρ - L| ≤ C' * ρ := by
    intro ρ hρ
    have hρ0 := hρ.1
    have est := grp_I_est hc hlip hρ0 hρ.2.le
    have e : F1 ρ / ρ - L = -(((∫ t in (0:ℝ)..ρ, t ^ 2 * h t) - h 0 * ρ ^ 3 / 3) / ρ ^ 3) := by
      simp only [hF1d, hL]; field_simp; ring
    rw [e, abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < ρ ^ 3), div_le_iff₀ (by positivity)]
    calc _ ≤ C * ρ ^ 4 := est
      _ ≤ C' * ρ * ρ ^ 3 := by
        have : C * ρ ^ 4 = C * ρ * ρ ^ 3 := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hρ0.le
        simp only [hC']; linarith [abs_nonneg (h 0)]
  have hK : ∀ ρ ∈ Ioo (0:ℝ) 1, |F2 ρ - F1 ρ / ρ| ≤ C' * ρ := by
    intro ρ hρ
    have hρ0 := hρ.1
    have est := grp_I_est hc hlip hρ0 hρ.2.le
    have hl := hlip ρ ⟨hρ0.le, hρ.2.le⟩
    have e : F2 ρ - F1 ρ / ρ = -(h ρ - h 0) +
        3 * (((∫ t in (0:ℝ)..ρ, t ^ 2 * h t) - h 0 * ρ ^ 3 / 3) / ρ ^ 3) := by
      simp only [hF1d, hF2d]; field_simp; ring
    have b2 : |((∫ t in (0:ℝ)..ρ, t ^ 2 * h t) - h 0 * ρ ^ 3 / 3) / ρ ^ 3| ≤ C * ρ := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ρ ^ 3), div_le_iff₀ (by positivity)]
      calc _ ≤ C * ρ ^ 4 := est
        _ = C * ρ * ρ ^ 3 := by ring
    rw [e]
    calc _ ≤ |-(h ρ - h 0)| + |3 * (((∫ t in (0:ℝ)..ρ, t ^ 2 * h t) - h 0 * ρ ^ 3 / 3) / ρ ^ 3)| :=
          abs_add_le _ _
      _ ≤ C * ρ + 3 * (C * ρ) := by
          rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
          linarith
      _ ≤ C' * ρ := by
          simp only [hC']; nlinarith [abs_nonneg (h 0)]
  have hquad : ∀ ρ ∈ Ico (0:ℝ) 1, |P h ρ - P h 0| ≤ C' * ρ ^ 2 := by
    intro ρ hρ
    calc _ ≤ (|h 0| + C) * ρ ^ 2 := grp_quad hc hlip ⟨hρ.1, hρ.2.le⟩
      _ ≤ C' * ρ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg ρ)
          simp only [hC']; linarith
  have hR0 : (0:ℝ) < 1 := one_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hx0 : x = 0
    · subst hx0
      exact Checked.Math.RadialC2.contDiffAt_zero_radial hR0 hF1 hF2 hF2c hM hK hquad
    · have hr : ‖x‖ ∈ Ioo (0:ℝ) 1 := ⟨norm_pos_iff.2 hx0, hx⟩
      have hFc : ContDiffOn ℝ 2 (P h) (Ioo 0 1) :=
        Checked.Math.GelfandPDEExists.contDiffOn_two_of_derivs isOpen_Ioo hF1 hF2 hF2c
      exact (hFc.contDiffAt (isOpen_Ioo.mem_nhds hr)).comp x (contDiffAt_norm ℝ hx0)
  · exact (grp_continuousOn hc hlip).comp continuous_norm.continuousOn (fun x hx =>
      ⟨norm_nonneg x, mem_closedBall_zero_iff.1 hx⟩)
  · intro x hx
    simp [P, hx]
  · intro x hx
    rw [mem_ball_zero_iff] at hx
    by_cases hx0 : x = 0
    · subst hx0
      rw [Checked.Math.RadialC2.laplacian_radial_zero hR0 hF1 hF2 hM hquad, finrank_euclideanSpace_fin]
      simp only [norm_zero, hL]
      push_cast
      ring
    · have hr : ‖x‖ ∈ Ioo (0:ℝ) 1 := ⟨norm_pos_iff.2 hx0, hx⟩
      have hL' := Checked.Math.RadialLaplacian.laplacian_radial (f := P h) (f' := F1)
        (f'' := F2 ‖x‖) hx0
        (by filter_upwards [isOpen_Ioo.mem_nhds hr] with ρ hρ using hF1 ρ hρ)
        (hF2 _ hr)
      rw [hL', finrank_euclideanSpace_fin]
      have hr0 : 0 < ‖x‖ := hr.1
      simp only [hF1d, hF2d]
      push_cast
      field_simp
      ring

theorem P_mono {h k : ℝ → ℝ} (hh : Continuous h) (hk : Continuous k)
    (hle : ∀ t ∈ Set.Icc (0:ℝ) 1, h t ≤ k t)
    {r : ℝ} (hr : r ∈ Set.Icc (0:ℝ) 1) : P h r ≤ P k r := by
  have ch : Continuous fun t : ℝ => (t - t ^ 2) * h t := (continuous_id.sub (continuous_pow 2)).mul hh
  have ck : Continuous fun t : ℝ => (t - t ^ 2) * k t := (continuous_id.sub (continuous_pow 2)).mul hk
  rcases eq_or_lt_of_le hr.1 with h0 | hr0
  · subst h0
    simp only [P, inv_zero, intervalIntegral.integral_same, mul_zero, zero_add]
    apply intervalIntegral.integral_mono_on zero_le_one
      (ch.intervalIntegrable 0 1) (ck.intervalIntegrable 0 1)
    intro t ht
    apply mul_le_mul_of_nonneg_left (hle t ht)
    nlinarith [ht.1, ht.2]
  unfold P
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left
    · apply intervalIntegral.integral_mono_on hr0.le
        (((continuous_pow 2).mul hh).intervalIntegrable 0 r)
        (((continuous_pow 2).mul hk).intervalIntegrable 0 r)
      intro t ht
      exact mul_le_mul_of_nonneg_left (hle t ⟨ht.1, ht.2.trans hr.2⟩) (sq_nonneg t)
    · rw [sub_nonneg]; exact one_le_inv₀ hr0 |>.2 hr.2
  · apply intervalIntegral.integral_mono_on hr.2
      (ch.intervalIntegrable r 1) (ck.intervalIntegrable r 1)
    intro t ht
    apply mul_le_mul_of_nonneg_left (hle t ⟨hr.1.trans ht.1, ht.2⟩)
    nlinarith [ht.1, ht.2, hr.1]

end Checked.Math.GRadialPoisson
