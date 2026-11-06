import Mathlib

/-! C² regularity of a radial function at the origin (helper for the existence direction of the
Gelfand PDE, run 2026-11-06T1628Z): if F' = F1 and F1' = F2 on (0, R) with F2 continuous there,
|F1(ρ)/ρ − L| ≤ Cρ, |F2(ρ) − F1(ρ)/ρ| ≤ Cρ and |F(ρ) − F(0)| ≤ Cρ², then y ↦ F ‖y‖ is C² at 0 in
any real inner product space. The first and second derivatives are explicit:
y ↦ M(‖y‖)·⟨y, ·⟩ with M = F1/ρ (L at 0), and M(‖y‖)·⟨·,·⟩ + K(‖y‖)/‖y‖·⟨y, ·⟩⟨y, ·⟩.
Instance note: on `E →L[ℝ] E →L[ℝ] ℝ` instance search does not find `ContinuousAdd` and algebraic
rewriting (`add_zero`, `sub_smul`, `norm_add_le`) fails to unify; bound norms there with
`ContinuousLinearMap.opNorm_le_bound` twice and evaluate on vectors instead. -/

namespace Work.Math.RadialC2
open Filter Topology Asymptotics Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_zero_of_sq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} {g' : E →L[ℝ] G} (C : ℝ)
    (h : ∀ᶠ y in 𝓝 (0 : E), ‖g y - g 0 - g' y‖ ≤ C * ‖y‖ ^ 2) : HasFDerivAt g g' 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  have hO : (fun y : E => g y - g 0 - g' y) =O[𝓝 0] fun y => ‖y‖ ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [h] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hy
  exact hO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_norm' {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  have h2 := (Real.hasDerivAt_sqrt hx2).comp_hasFDerivAt x h1
  have e : (fun y : E => √(‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  rw [Function.comp_def, e] at h2
  convert h2 using 1
  rw [Real.sqrt_sq (norm_nonneg x)]
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  ext v
  simp [smul_eq_mul]
  field_simp

/-- The inner product as a continuous bilinear map, typed as an ordinary `E →L[ℝ] E →L[ℝ] ℝ`. -/
noncomputable def IL : E →L[ℝ] E →L[ℝ] ℝ := by exact innerSL ℝ

omit [FiniteDimensional ℝ E] in
theorem IL_apply (y : E) : IL y = innerSL ℝ y := rfl

omit [FiniteDimensional ℝ E] in
theorem norm_IL_apply (y : E) : ‖IL y‖ = ‖y‖ := by rw [IL_apply, innerSL_apply_norm]

/-- The profile quotient `M ρ = F1 ρ / ρ`, with value `L` at 0. -/
noncomputable def Mq (F1 : ℝ → ℝ) (L : ℝ) (ρ : ℝ) : ℝ := if ρ = 0 then L else F1 ρ / ρ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
omit [FiniteDimensional ℝ E] in
theorem contDiffAt_zero_radial {F F1 F2 : ℝ → ℝ} {L C R : ℝ} (hR : 0 < R)
    (hF1 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F (F1 ρ) ρ)
    (hF2 : ∀ ρ ∈ Ioo 0 R, HasDerivAt F1 (F2 ρ) ρ)
    (hF2c : ContinuousOn F2 (Ioo 0 R))
    (hM : ∀ ρ ∈ Ioo 0 R, |F1 ρ / ρ - L| ≤ C * ρ)
    (hK : ∀ ρ ∈ Ioo 0 R, |F2 ρ - F1 ρ / ρ| ≤ C * ρ)
    (hquad : ∀ ρ ∈ Ico 0 R, |F ρ - F 0| ≤ C * ρ ^ 2) :
    ContDiffAt ℝ 2 (fun y : E => F ‖y‖) 0 := by
  set M := Mq F1 L with hMdef
  set K : ℝ → ℝ := fun ρ => (F2 ρ - F1 ρ / ρ) / ρ with hKdef
  set f' : E → E →L[ℝ] ℝ := fun y => M ‖y‖ • IL y with hf'
  set g' : E → E →L[ℝ] (E →L[ℝ] ℝ) := fun y =>
    M ‖y‖ • IL + (K ‖y‖ • ‖y‖⁻¹ • IL y).smulRight (IL y) with hg'
  have hball : Metric.ball (0 : E) R ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds 0 hR
  have Mpos : ∀ ρ, ρ ≠ 0 → M ρ = F1 ρ / ρ := fun ρ h => by simp [hMdef, Mq, h]
  have M0 : M 0 = L := by simp [hMdef, Mq]
  -- M is F1/id near any r > 0
  have Mev : ∀ r ∈ Ioo 0 R, M =ᶠ[𝓝 r] fun ρ => F1 ρ / ρ := fun r hr => by
    filter_upwards [eventually_ne_nhds hr.1.ne'] with ρ hρ using Mpos ρ hρ
  have hMd : ∀ r ∈ Ioo 0 R, HasDerivAt M (K r) r := fun r hr => by
    have h := (hF2 r hr).div (hasDerivAt_id r) hr.1.ne'
    have h' := h.congr_of_eventuallyEq (Mev r hr)
    convert h' using 1
    have := hr.1.ne'
    simp only [hKdef, id]
    field_simp
  -- first derivative everywhere in the ball
  have d1 : ∀ y ∈ Metric.ball (0 : E) R, HasFDerivAt (fun y : E => F ‖y‖) (f' y) y := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    by_cases hy0 : y = 0
    · subst hy0
      have e : f' 0 = 0 := by simp [hf']
      rw [e]
      refine hasFDerivAt_zero_of_sq C ?_
      filter_upwards [hball] with z hz
      rw [mem_ball_zero_iff] at hz
      simpa [Real.norm_eq_abs] using hquad ‖z‖ ⟨norm_nonneg z, hz⟩
    · have hr : ‖y‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hy0, hy⟩
      have h := (hF1 ‖y‖ hr).comp_hasFDerivAt y (hasFDerivAt_norm' hy0)
      rw [Function.comp_def] at h
      convert h using 1
      simp only [hf', Mpos _ hr.1.ne', smul_smul]
      congr 1
  -- second derivative everywhere in the ball
  have d2 : ∀ y ∈ Metric.ball (0 : E) R, HasFDerivAt f' (g' y) y := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    by_cases hy0 : y = 0
    · subst hy0
      have e : g' 0 = L • IL := by ext v w; simp [hg', M0]
      rw [e]
      refine hasFDerivAt_zero_of_sq C ?_
      filter_upwards [hball] with z hz
      rw [mem_ball_zero_iff] at hz
      have f0 : f' 0 = 0 := by simp [hf']
      rw [f0, sub_zero]
      by_cases hz0 : z = 0
      · subst hz0; simp [hf']
      have hr : ‖z‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hz0, hz⟩
      have e2 : f' z - (L • IL) z = (F1 ‖z‖ / ‖z‖ - L) • IL z := by
        simp only [hf', Mpos _ hr.1.ne', ContinuousLinearMap.smul_apply]
        exact (sub_smul _ _ _).symm
      rw [e2, norm_smul, norm_IL_apply, Real.norm_eq_abs]
      have := hM _ hr
      calc |F1 ‖z‖ / ‖z‖ - L| * ‖z‖ ≤ C * ‖z‖ * ‖z‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg z)
        _ = C * ‖z‖ ^ 2 := by ring
    · have hr : ‖y‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hy0, hy⟩
      have hc := (hMd ‖y‖ hr).comp_hasFDerivAt y (hasFDerivAt_norm' hy0)
      rw [Function.comp_def] at hc
      have hL : HasFDerivAt (fun y : E => IL y) IL y := IL.hasFDerivAt
      exact hc.fun_smul hL
  -- continuity of the second derivative on the ball
  have cg : ContinuousOn g' (Metric.ball (0 : E) R) := by
    intro y hy
    rw [mem_ball_zero_iff] at hy
    refine ContinuousAt.continuousWithinAt ?_
    by_cases hy0 : y = 0
    · subst hy0
      have e : g' 0 = L • IL := by ext v w; simp [hg', M0]
      rw [ContinuousAt, e]
      refine (tendsto_iff_norm_sub_tendsto_zero (f := g')).2 ?_
      refine squeeze_zero' (Eventually.of_forall fun z => by exact norm_nonneg (g' z - L • IL)) ?_
        (g := fun z : E => (2 * |C|) * ‖z‖) ?_
      · filter_upwards [hball] with z hz
        rw [mem_ball_zero_iff] at hz
        have hX : 0 ≤ 2 * |C| * ‖z‖ := by positivity
        refine ContinuousLinearMap.opNorm_le_bound _ hX fun v => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
        by_cases hz0 : z = 0
        · subst hz0
          have : ((g' 0 - L • IL : E →L[ℝ] E →L[ℝ] ℝ) v) w = 0 := by rw [e]; simp
          rw [this]; simp
        have hr : ‖z‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hz0, hz⟩
        have hz' : 0 < ‖z‖ := hr.1
        have ev : ((g' z - L • IL : E →L[ℝ] E →L[ℝ] ℝ) v) w = (F1 ‖z‖ / ‖z‖ - L) * inner ℝ v w +
            K ‖z‖ * ‖z‖⁻¹ * (inner ℝ z v * inner ℝ z w) := by
          simp [hg', Mpos _ hr.1.ne', IL_apply, innerSL_apply_apply]
          ring
        rw [ev, Real.norm_eq_abs]
        have h1 := hM _ hr
        have h2 : |K ‖z‖| ≤ C := by
          simp only [hKdef, abs_div, abs_of_pos hz']
          rw [div_le_iff₀ hz']; exact hK _ hr
        have hvw := abs_real_inner_le_norm v w
        have hzv := abs_real_inner_le_norm z v
        have hzw := abs_real_inner_le_norm z w
        have hC : |C| = C := abs_of_nonneg ((abs_nonneg _).trans h2)
        rw [hC]
        have t1 : |(F1 ‖z‖ / ‖z‖ - L) * inner ℝ v w| ≤ C * ‖z‖ * (‖v‖ * ‖w‖) := by
          have hCn : 0 ≤ C := (abs_nonneg _).trans h2
          rw [abs_mul]; exact mul_le_mul h1 hvw (abs_nonneg _) (by positivity)
        have t2 : |K ‖z‖ * ‖z‖⁻¹ * (inner ℝ z v * inner ℝ z w)| ≤ C * ‖z‖ * (‖v‖ * ‖w‖) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hz')]
          have h3 : |inner ℝ z v| * |inner ℝ z w| ≤ (‖z‖ * ‖v‖) * (‖z‖ * ‖w‖) :=
            mul_le_mul hzv hzw (abs_nonneg _) (by positivity)
          have e4 : C * ‖z‖ * (‖v‖ * ‖w‖) = C * ‖z‖⁻¹ * ((‖z‖ * ‖v‖) * (‖z‖ * ‖w‖)) := by
            field_simp
          rw [e4]
          have hCn : 0 ≤ C := (abs_nonneg _).trans h2
          exact mul_le_mul (mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hz'.le)) h3
            (by positivity) (by positivity)
        calc _ ≤ _ := abs_add_le _ _
          _ ≤ C * ‖z‖ * (‖v‖ * ‖w‖) + C * ‖z‖ * (‖v‖ * ‖w‖) := add_le_add t1 t2
          _ = 2 * C * ‖z‖ * ‖v‖ * ‖w‖ := by ring
      · have : Tendsto (fun z : E => ‖z‖) (𝓝 0) (𝓝 0) := by
          simpa using (continuous_norm.tendsto (0 : E))
        simpa using this.const_mul (2 * |C|)
    · have hr : ‖y‖ ∈ Ioo 0 R := ⟨norm_pos_iff.2 hy0, hy⟩
      have cn : ContinuousAt (fun z : E => ‖z‖) y := continuous_norm.continuousAt
      have cM : ContinuousAt (fun z : E => M ‖z‖) y :=
        ((hMd _ hr).continuousAt).comp cn
      have cK0 : ContinuousAt K ‖y‖ := by
        have hF2a : ContinuousAt F2 ‖y‖ := hF2c.continuousAt (isOpen_Ioo.mem_nhds hr)
        have hF1a : ContinuousAt F1 ‖y‖ := (hF2 _ hr).continuousAt
        exact ((hF2a.sub (hF1a.div continuousAt_id hr.1.ne')).div continuousAt_id hr.1.ne')
      have cK : ContinuousAt (fun z : E => K ‖z‖) y := cK0.comp cn
      have cinv : ContinuousAt (fun z : E => ‖z‖⁻¹) y := cn.inv₀ hr.1.ne'
      have cI : ContinuousAt (fun z : E => IL z) y := IL.continuous.continuousAt
      have c1 : ContinuousAt (fun z : E => K ‖z‖ • ‖z‖⁻¹ • IL z) y :=
        cK.smul (cinv.smul cI)
      have c2 : ContinuousAt (fun z : E =>
          (K ‖z‖ • ‖z‖⁻¹ • IL z).smulRight (IL z)) y := by
        exact (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ)).continuous.continuousAt.comp₂ c1 cI
      have : ContinuousAdd (E →L[ℝ] E →L[ℝ] ℝ) :=
        @IsTopologicalAddGroup.toContinuousAdd _ _ _ ContinuousLinearMap.isTopologicalAddGroup
      exact (cM.smul continuousAt_const).add c2
  -- assemble
  have h2 : (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
  rw [h2, contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨f', ⟨_, hball, d1⟩, ?_⟩
  have h1 : ((1 : ℕ) : WithTop ℕ∞) = ((0 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
  rw [h1, contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨g', ⟨_, hball, d2⟩, ?_⟩
  exact contDiffAt_zero.2 ⟨_, hball, cg⟩

end Work.Math.RadialC2
