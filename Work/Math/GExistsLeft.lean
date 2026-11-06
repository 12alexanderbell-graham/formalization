import Mathlib
import Work.Math.GExistsRight

/-!
# Gelfand problem: a solution regular at the singular point, on [0, 1/2]

Banach fixed point (Mathlib `ContractingWith.fixedPoint`) of the Volterra map
  (T f)(x) = −x² ∫₀¹ u(1 − u) g(f(xu)) du,  g = exp ∘ (clamp to [−1, 1]),
on the bounded continuous functions on [0, 1/2], adapted from `Work/Math/LEExistsLeft.lean`
(θ³ → e^w, θ(0) = 1 → w(0) = 0). |g| ≤ 3, g is 3-Lipschitz, so T is Lipschitz with constant
1/8 ≤ 1/4 and |w| ≤ 1/8 keeps the clamp inactive; g > 0 gives w ≤ 0 and φ ≤ 0.
-/

namespace Work.Math.GExistsLeft
open Set Work.Math.GExistsRight MeasureTheory Filter Topology

/-- Clamped exponential. -/
noncomputable def g (y : ℝ) : ℝ := Real.exp (cl 1 y)

theorem continuous_g : Continuous g := Real.continuous_exp.comp (continuous_cl _)

theorem g_pos (y : ℝ) : 0 < g y := Real.exp_pos _

theorem abs_g_le (y : ℝ) : |g y| ≤ 3 := by
  have h := (abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) y)).2
  unfold g; rw [abs_of_pos (Real.exp_pos _)]
  calc Real.exp (cl 1 y) ≤ Real.exp 1 := Real.exp_le_exp.2 h
    _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith

theorem g_sub (y z : ℝ) : |g y - g z| ≤ 3 * |y - z| := by
  unfold g
  have hy := (abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) y)).2
  have hz := (abs_le.1 (abs_cl_le (by norm_num : (0 : ℝ) ≤ 1) z)).2
  have h := exp_sub_le_of_le hy hz
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  calc |Real.exp (cl 1 y) - Real.exp (cl 1 z)| ≤ Real.exp 1 * |cl 1 y - cl 1 z| := h
    _ ≤ 3 * |y - z| := mul_le_mul he (cl_sub _ _ _) (abs_nonneg _) (by norm_num)

theorem g_of_abs_le {y : ℝ} (h : |y| ≤ 1) : g y = Real.exp y := by
  unfold g; rw [cl_of_abs_le h]

theorem h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num

/-- The space of the fixed-point argument. -/
abbrev Sp := BoundedContinuousFunction (Icc (0 : ℝ) (1 / 2)) ℝ

/-- Extension of a function on [0, 1/2] to ℝ (constant outside). -/
noncomputable def ext (f : Sp) : ℝ → ℝ := IccExtend h12 f

theorem continuous_ext (f : Sp) : Continuous (ext f) := f.continuous.Icc_extend'

theorem dist_ext (f h : Sp) (y : ℝ) : |ext f y - ext h y| ≤ dist f h := by
  rw [← Real.dist_eq]
  exact BoundedContinuousFunction.dist_coe_le_dist _

/-- The scaled Volterra integral. -/
noncomputable def J (k : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, u * (1 - u) * g (k (x * u))

theorem continuous_J {k : ℝ → ℝ} (hk : Continuous k) : Continuous (J k) := by
  unfold J
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (by
    have : Continuous fun p : ℝ × ℝ => p.2 * (1 - p.2) * g (k (p.1 * p.2)) :=
      (continuous_snd.mul (continuous_const.sub continuous_snd)).mul
        (continuous_g.comp (hk.comp (continuous_fst.mul continuous_snd)))
    exact this)

theorem int_w : ∫ u in (0 : ℝ)..1, u * (1 - u) = 1 / 6 := by
  have : (fun u : ℝ => u * (1 - u)) = fun u => u - u ^ 2 := by funext u; ring
  rw [this, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
    ((continuous_pow 2).intervalIntegrable _ _)]
  simp; norm_num

theorem int_sq : ∫ u in (0 : ℝ)..1, u ^ 2 = 1 / 3 := by
  simp; norm_num

theorem w_nonneg {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) : 0 ≤ u * (1 - u) :=
  mul_nonneg hu.1.le (by linarith [hu.2])

theorem abs_J_le {k : ℝ → ℝ} (hk : Continuous k) (x : ℝ) : |J k x| ≤ 0.5 := by
  unfold J
  rw [← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun u => u * (1 - u) * g (k (x * u))) (g := fun u => u * (1 - u) * 3) zero_le_one
    (ae_of_all _ fun u hu => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (w_nonneg hu)]
      exact mul_le_mul_of_nonneg_left (abs_g_le _) (w_nonneg hu))
    ((show Continuous fun u : ℝ => u * (1 - u) * 3 by fun_prop).intervalIntegrable _ _)
  refine hb.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, int_w]; norm_num

theorem J_sub_le {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k') {d : ℝ}
    (hd : ∀ y, |k y - k' y| ≤ d) (x : ℝ) : |J k x - J k' x| ≤ 1 / 2 * d := by
  unfold J
  have c1 : Continuous fun u : ℝ => u * (1 - u) * g (k (x * u)) :=
    (continuous_id.mul (continuous_const.sub continuous_id)).mul
      (continuous_g.comp (hk.comp (continuous_const.mul continuous_id)))
  have i1 := c1.intervalIntegrable (μ := volume) 0 1
  have c2 : Continuous fun u : ℝ => u * (1 - u) * g (k' (x * u)) :=
    (continuous_id.mul (continuous_const.sub continuous_id)).mul
      (continuous_g.comp (hk'.comp (continuous_const.mul continuous_id)))
  have i2 := c2.intervalIntegrable (μ := volume) 0 1
  rw [← intervalIntegral.integral_sub i1 i2, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun u => u * (1 - u) * g (k (x * u)) - u * (1 - u) * g (k' (x * u)))
    (g := fun u => u * (1 - u) * (3 * d)) zero_le_one
    (ae_of_all _ fun u hu => by
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (w_nonneg hu)]
      refine mul_le_mul_of_nonneg_left ((g_sub _ _).trans ?_) (w_nonneg hu)
      exact mul_le_mul_of_nonneg_left (hd _) (by norm_num))
    ((show Continuous fun u : ℝ => u * (1 - u) * (3 * d) by fun_prop).intervalIntegrable _ _)
  refine hb.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, int_w]; ring

/-- The Volterra map. -/
noncomputable def Tmap (f : Sp) : Sp :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : Icc (0 : ℝ) (1 / 2) => 0 - (x : ℝ) ^ 2 * J (ext f) x,
      continuous_const.sub ((continuous_subtype_val.pow 2).mul
        ((continuous_J (continuous_ext f)).comp continuous_subtype_val))⟩

theorem Tmap_apply (f : Sp) (x : Icc (0 : ℝ) (1 / 2)) :
    Tmap f x = 0 - (x : ℝ) ^ 2 * J (ext f) x := rfl

theorem sq_le_quarter {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) : x ^ 2 ≤ 1 / 4 := by
  nlinarith [hx.1, hx.2]

theorem contracting : ContractingWith (1 / 4) Tmap := by
  constructor
  · exact NNReal.coe_lt_coe.1 (by norm_num)
  · refine LipschitzWith.of_dist_le_mul fun f h => ?_
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro x
    rw [Tmap_apply, Tmap_apply, Real.dist_eq]
    have hJ := J_sub_le (continuous_ext f) (continuous_ext h) (dist_ext f h) x
    have e : (0 - (x : ℝ) ^ 2 * J (ext f) x) - (0 - (x : ℝ) ^ 2 * J (ext h) x)
        = -((x : ℝ) ^ 2 * (J (ext f) x - J (ext h) x)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hx2 := sq_le_quarter x.2
    have hc : ((1 / 4 : NNReal) : ℝ) = 1 / 4 := by norm_num
    rw [hc]
    nlinarith [abs_nonneg (J (ext f) x - J (ext h) x), dist_nonneg (x := f) (y := h),
      sq_nonneg (x : ℝ)]

/-- The fixed point. -/
noncomputable def θs : Sp := ContractingWith.fixedPoint Tmap contracting

/-- The solution on [0, 1/2] (extended constantly outside). -/
noncomputable def θL : ℝ → ℝ := ext θs

theorem continuous_θL : Continuous θL := continuous_ext _

theorem θL_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) : θL x = 0 - x ^ 2 * J θL x := by
  have hfix : Tmap θs = θs := contracting.fixedPoint_isFixedPt
  have h1 := DFunLike.congr_fun hfix ⟨x, hx⟩
  unfold θL ext
  rw [IccExtend_of_mem h12 _ hx, ← h1]
  rfl

theorem abs_θL_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) : |θL x| ≤ 0.125 := by
  rw [θL_eq hx]
  have hJ := abs_J_le continuous_θL x
  have hx2 := sq_le_quarter hx
  rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _)]
  nlinarith [abs_nonneg (J θL x), sq_nonneg x]

theorem J_nonneg {k : ℝ → ℝ} (x : ℝ) : 0 ≤ J k x := by
  unfold J
  refine intervalIntegral.integral_nonneg zero_le_one fun u hu => ?_
  exact mul_nonneg (mul_nonneg hu.1 (by linarith [hu.2])) (g_pos _).le

theorem θL_nonpos {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) : θL x ≤ 0 := by
  rw [θL_eq hx]
  have := J_nonneg (k := θL) x
  nlinarith [sq_nonneg x]

/-- g ∘ θL. -/
noncomputable def G (s : ℝ) : ℝ := g (θL s)

theorem continuous_G : Continuous G := continuous_g.comp continuous_θL

/-- The derivative: φ(x) = −x ∫₀¹ u² g(θ(xu)) du. -/
noncomputable def φL (x : ℝ) : ℝ := -(x * ∫ u in (0 : ℝ)..1, u ^ 2 * G (x * u))

theorem continuous_φL : Continuous φL := by
  unfold φL
  refine (continuous_id.mul ?_).neg
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (by
    have : Continuous fun p : ℝ × ℝ => p.2 ^ 2 * G (p.1 * p.2) :=
      (continuous_snd.pow 2).mul (continuous_G.comp (continuous_fst.mul continuous_snd))
    exact this)

theorem abs_φL_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) : |φL x| ≤ 0.5 := by
  unfold φL
  rw [abs_neg, abs_mul, abs_of_nonneg hx.1]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun u => u ^ 2 * G (x * u)) (g := fun u => u ^ 2 * 3) zero_le_one
    (ae_of_all _ fun u _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (abs_g_le _) (sq_nonneg _))
    ((show Continuous fun u : ℝ => u ^ 2 * 3 by fun_prop).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, int_sq, Real.norm_eq_abs] at hb
  have hx2 := hx.2
  nlinarith [abs_nonneg (∫ u in (0 : ℝ)..1, u ^ 2 * G (x * u)), hx.1]

/-- ∫₀^x s g(θ). -/
noncomputable def A (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, s * G s

/-- ∫₀^x s² g(θ). -/
noncomputable def B (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, s ^ 2 * G s

theorem hasDerivAt_A (x : ℝ) : HasDerivAt A (x * G x) x :=
  ((continuous_id.mul continuous_G).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem hasDerivAt_B (x : ℝ) : HasDerivAt B (x ^ 2 * G x) x :=
  (((continuous_pow 2).mul continuous_G).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem cont_sG : Continuous fun s => s * G s := continuous_id.mul continuous_G
theorem cont_s2G : Continuous fun s => s ^ 2 * G s := (continuous_pow 2).mul continuous_G

/-- Substitution s = xu in J. -/
theorem J_subst {x : ℝ} (hx : x ≠ 0) : x ^ 2 * J θL x = A x - x⁻¹ * B x := by
  unfold J
  have key := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun s => x⁻¹ * (s * G s) - (x⁻¹) ^ 2 * (s ^ 2 * G s)) hx
  rw [mul_zero, mul_one] at key
  have e1 : (∫ u in (0 : ℝ)..1, u * (1 - u) * g (θL (x * u)))
      = ∫ u in (0 : ℝ)..1, (x⁻¹ * (x * u * G (x * u)) - (x⁻¹) ^ 2 * ((x * u) ^ 2 * G (x * u))) :=
    intervalIntegral.integral_congr fun u _ => by simp only [G]; field_simp
  rw [e1, key,
    intervalIntegral.integral_sub ((cont_sG.intervalIntegrable _ _).const_mul _)
      ((cont_s2G.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold A B
  simp only [smul_eq_mul]
  field_simp

/-- Substitution s = xu in φ. -/
theorem φL_subst {x : ℝ} (hx : x ≠ 0) : φL x = -((x ^ 2)⁻¹ * B x) := by
  unfold φL
  have key := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun s => (x⁻¹) ^ 2 * (s ^ 2 * G s)) hx
  rw [mul_zero, mul_one] at key
  have e1 : (∫ u in (0 : ℝ)..1, u ^ 2 * G (x * u))
      = ∫ u in (0 : ℝ)..1, (x⁻¹) ^ 2 * ((x * u) ^ 2 * G (x * u)) :=
    intervalIntegral.integral_congr fun u _ => by field_simp
  rw [e1, key, intervalIntegral.integral_const_mul]
  unfold B
  simp only [smul_eq_mul]
  field_simp

theorem pos_mem_nhds {x : ℝ} (hx : 0 < x) :
    Ioc (0 : ℝ) (1 / 2) ∈ 𝓝[Icc (0 : ℝ) (1 / 2)] x :=
  mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, hx, fun y hy => ⟨hy.1, hy.2.2⟩⟩

theorem hasDerivAt_mul_cont {K : ℝ → ℝ} (hK : ContinuousAt K 0) :
    HasDerivAt (fun ε => ε * K ε) (K 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine (hK.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
  field_simp

theorem deriv_θL {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    HasDerivWithinAt θL (φL x) (Icc 0 (1 / 2)) x := by
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · subst h0
    have hK : ContinuousAt (fun y => y * J θL y) 0 :=
      (continuous_id.mul (continuous_J continuous_θL)).continuousAt
    have hd := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).sub (hasDerivAt_mul_cont hK)
    have hφ0 : φL 0 = 0 := by simp [φL]
    rw [hφ0]
    refine (hd.hasDerivWithinAt.congr (fun y hy => ?_) ?_).congr_deriv (by simp)
    · simp only [Pi.sub_apply]; rw [θL_eq hy]; ring
    · simp only [Pi.sub_apply]; rw [θL_eq hx]; ring
  · have hxne : x ≠ 0 := hpos.ne'
    have hd := (hasDerivAt_const x (0 : ℝ)).sub
      ((hasDerivAt_A x).sub ((hasDerivAt_inv hxne).mul (hasDerivAt_B x)))
    have hval : 0 - (x * G x - (-(x ^ 2)⁻¹ * B x + x⁻¹ * (x ^ 2 * G x))) = φL x := by
      rw [φL_subst hxne]; field_simp; ring
    rw [← hval]
    refine (hd.hasDerivWithinAt.congr (s := Ioc 0 (1 / 2)) (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin
      (pos_mem_nhds hpos)
    · simp only [Pi.sub_apply, Pi.mul_apply]; rw [θL_eq (Ioc_subset_Icc_self hy), J_subst hy.1.ne']
    · simp only [Pi.sub_apply, Pi.mul_apply]; rw [θL_eq hx, J_subst hxne]

theorem deriv_φL {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    HasDerivWithinAt φL (-(2 / x * φL x) - Real.exp (θL x)) (Icc 0 (1 / 2)) x := by
  have hxne : x ≠ 0 := hx.1.ne'
  have hd := (((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hxne)).mul (hasDerivAt_B x)).neg
  have hG : G x = Real.exp (θL x) := by
    unfold G; rw [g_of_abs_le ((abs_θL_le (Ioc_subset_Icc_self hx)).trans (by norm_num))]
  have hval : -(-(↑2 * x ^ (2 - 1)) / (x ^ 2) ^ 2 * B x + (x ^ 2)⁻¹ * (x ^ 2 * G x))
      = -(2 / x * φL x) - Real.exp (θL x) := by
    rw [φL_subst hxne, hG]; field_simp; ring
  rw [← hval]
  refine (hd.hasDerivWithinAt.congr (s := Ioc 0 (1 / 2)) (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin
    (pos_mem_nhds hx.1)
  · simp only [Pi.neg_apply, Pi.mul_apply, Pi.inv_apply]; rw [φL_subst hy.1.ne']
  · simp only [Pi.neg_apply, Pi.mul_apply, Pi.inv_apply]; rw [φL_subst hxne]

theorem θL_zero : θL 0 = 0 := by
  rw [θL_eq ⟨le_rfl, by norm_num⟩]; ring

theorem φL_nonpos {x : ℝ} (hx : 0 ≤ x) : φL x ≤ 0 := by
  unfold φL
  have : 0 ≤ ∫ u in (0 : ℝ)..1, u ^ 2 * G (x * u) :=
    intervalIntegral.integral_nonneg zero_le_one fun u _ =>
      mul_nonneg (sq_nonneg u) (g_pos _).le
  have := mul_nonneg hx this
  linarith

/-- The left piece: a solution regular at s = 0 on [0, 1/2], with w(1/2) ≤ 0 and
−1 ≤ φ(1/2) ≤ 0. -/
theorem exists_left : ∃ w φ : ℝ → ℝ, w 0 = 0 ∧ Continuous φ ∧
    w (1 / 2) ≤ 0 ∧ φ (1 / 2) ≤ 0 ∧ -1 ≤ φ (1 / 2) ∧
    (∀ x ∈ Icc (0 : ℝ) (1 / 2), HasDerivWithinAt w (φ x) (Icc 0 (1 / 2)) x) ∧
    (∀ x ∈ Ioc (0 : ℝ) (1 / 2),
      HasDerivWithinAt φ (-(2 / x * φ x) - Real.exp (w x)) (Icc 0 (1 / 2)) x) :=
  ⟨θL, φL, θL_zero, continuous_φL, θL_nonpos ⟨h12, le_rfl⟩, φL_nonpos h12,
    by have := (abs_le.1 (abs_φL_le ⟨h12, le_rfl⟩)).1; linarith,
    fun _ hx => deriv_θL hx, fun _ hx => deriv_φL hx⟩

end Work.Math.GExistsLeft

#print axioms Work.Math.GExistsLeft.exists_left
