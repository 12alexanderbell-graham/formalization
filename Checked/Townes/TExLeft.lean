import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
/-! Townes ground state, `TExLeft`: a family of solutions of the Townes radial equation regular at the centre, as fixed points of a contraction depending on the central value. Promoted from `Work/Townes/TExLeft.lean`. -/

namespace Checked.Townes.TExLeft
open Set MeasureTheory Filter Topology

/-- Clamp to [−3, 3]. -/
noncomputable def cl (y : ℝ) : ℝ := max (-3) (min 3 y)

theorem continuous_cl : Continuous cl :=
  continuous_const.max (continuous_const.min continuous_id)

theorem cl_sub (y z : ℝ) : |cl y - cl z| ≤ |y - z| := by
  unfold cl
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem abs_cl_le (y : ℝ) : |cl y| ≤ 3 := by
  unfold cl; rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem cl_of_abs_le {y : ℝ} (h : |y| ≤ 3) : cl y = y := by
  unfold cl; rw [abs_le] at h; rw [min_eq_right h.2, max_eq_right h.1]

/-- Clamped nonlinearity y − y³. -/
noncomputable def g (y : ℝ) : ℝ := cl y - cl y ^ 3

theorem continuous_g : Continuous g := continuous_cl.sub (continuous_cl.pow 3)

theorem poly_diff (a b : ℝ) (ha : |a| ≤ 3) (hb : |b| ≤ 3) :
    |(a - a ^ 3) - (b - b ^ 3)| ≤ 26 * |a - b| := by
  have e : (a - a ^ 3) - (b - b ^ 3) = (1 - (a ^ 2 + a * b + b ^ 2)) * (a - b) := by ring
  rw [e, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_le] at ha hb ⊢
  have ha2 : a ^ 2 ≤ 9 := by nlinarith
  have hb2 : b ^ 2 ≤ 9 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

theorem g_sub (y z : ℝ) : |g y - g z| ≤ 26 * |y - z| := by
  unfold g
  exact (poly_diff _ _ (abs_cl_le y) (abs_cl_le z)).trans
    (mul_le_mul_of_nonneg_left (cl_sub _ _) (by norm_num))

theorem abs_g_le (y : ℝ) : |g y| ≤ 24 := by
  unfold g
  have h := abs_le.1 (abs_cl_le y)
  set a := cl y
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 - a) (by nlinarith : (0 : ℝ) ≤ a ^ 2 + 3 * a + 8)]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a + 3) (by nlinarith : (0 : ℝ) ≤ a ^ 2 - 3 * a + 8)]

theorem g_le_neg_one {y : ℝ} (h1 : 3 / 2 ≤ y) (h2 : y ≤ 3) : g y ≤ -1 := by
  have hy : |y| ≤ 3 := abs_le.2 ⟨by linarith, h2⟩
  unfold g; rw [cl_of_abs_le hy]
  have : 9 / 4 * y ≤ y ^ 2 * y := mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
  nlinarith

theorem w_le {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : Real.negMulLog u ≤ 1 - u := by
  rcases eq_or_lt_of_le hu.1 with h | h
  · subst h; simp [Real.negMulLog]
  · have hl := Real.log_le_sub_one_of_pos (inv_pos.2 h)
    rw [Real.log_inv] at hl
    unfold Real.negMulLog
    have : u * (-Real.log u) ≤ u * (u⁻¹ - 1) := mul_le_mul_of_nonneg_left hl h.le
    rw [mul_sub, mul_inv_cancel₀ h.ne'] at this
    linarith

theorem w_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 0 ≤ Real.negMulLog u :=
  Real.negMulLog_nonneg hu.1 hu.2

theorem mem_of_uIoc {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) : u ∈ Icc (0 : ℝ) 1 :=
  Ioc_subset_Icc_self hu

theorem int_1mu : ∫ u in (0 : ℝ)..1, (1 - u) = 1 / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp; norm_num

theorem int_u : ∫ u in (0 : ℝ)..1, u = 1 / 2 := by
  simp

theorem h15 : (0 : ℝ) ≤ 1 / 5 := by norm_num

/-- The space of the fixed-point argument. -/
abbrev Sp := BoundedContinuousFunction (Icc (0 : ℝ) (1 / 5)) ℝ

/-- Extension of a function on [0, 1/5] to ℝ (constant outside). -/
noncomputable def ext (f : Sp) : ℝ → ℝ := IccExtend h15 f

theorem continuous_ext (f : Sp) : Continuous (ext f) := f.continuous.Icc_extend'

theorem dist_ext (f h : Sp) (y : ℝ) : |ext f y - ext h y| ≤ dist f h := by
  rw [← Real.dist_eq]
  exact BoundedContinuousFunction.dist_coe_le_dist _

/-- The scaled Volterra integral with the dimension-2 kernel −u log u. -/
noncomputable def J (k : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, Real.negMulLog u * g (k (x * u))

theorem continuous_J {k : ℝ → ℝ} (hk : Continuous k) : Continuous (J k) := by
  unfold J
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (by
    have : Continuous fun p : ℝ × ℝ => Real.negMulLog p.2 * g (k (p.1 * p.2)) :=
      (Real.continuous_negMulLog.comp continuous_snd).mul
        (continuous_g.comp (hk.comp (continuous_fst.mul continuous_snd)))
    exact this)

theorem cont_kernel {k : ℝ → ℝ} (hk : Continuous k) (x : ℝ) :
    Continuous fun u : ℝ => Real.negMulLog u * g (k (x * u)) :=
  Real.continuous_negMulLog.mul (continuous_g.comp (hk.comp (continuous_const.mul continuous_id)))

theorem abs_J_le {k : ℝ → ℝ} (_hk : Continuous k) (x : ℝ) : |J k x| ≤ 12 := by
  unfold J
  rw [← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun u => Real.negMulLog u * g (k (x * u))) (g := fun u => (1 - u) * 24) zero_le_one
    (ae_of_all _ fun u hu => by
      have hu' := mem_of_uIoc hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (w_nonneg hu')]
      exact mul_le_mul (w_le hu') (abs_g_le _) (abs_nonneg _) (by linarith [hu'.2]))
    ((show Continuous fun u : ℝ => (1 - u) * 24 by fun_prop).intervalIntegrable _ _)
  refine hb.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, int_1mu]; norm_num

theorem J_sub_le {k k' : ℝ → ℝ} (hk : Continuous k) (hk' : Continuous k') {d : ℝ}
    (hd : ∀ y, |k y - k' y| ≤ d) (x : ℝ) : |J k x - J k' x| ≤ 13 * d := by
  unfold J
  have i1 := (cont_kernel hk x).intervalIntegrable (μ := volume) 0 1
  have i2 := (cont_kernel hk' x).intervalIntegrable (μ := volume) 0 1
  rw [← intervalIntegral.integral_sub i1 i2, ← Real.norm_eq_abs]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun u => Real.negMulLog u * g (k (x * u)) - Real.negMulLog u * g (k' (x * u)))
    (g := fun u => (1 - u) * (26 * d)) zero_le_one
    (ae_of_all _ fun u hu => by
      have hu' := mem_of_uIoc hu
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (w_nonneg hu')]
      refine mul_le_mul (w_le hu') ((g_sub _ _).trans ?_) (abs_nonneg _) (by linarith [hu'.2])
      exact mul_le_mul_of_nonneg_left (hd _) (by norm_num))
    ((show Continuous fun u : ℝ => (1 - u) * (26 * d) by fun_prop).intervalIntegrable _ _)
  refine hb.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, int_1mu]; ring

/-- The Volterra map with central value c. -/
noncomputable def Tmap (c : ℝ) (f : Sp) : Sp :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x : Icc (0 : ℝ) (1 / 5) => c + (x : ℝ) ^ 2 * J (ext f) x,
      continuous_const.add ((continuous_subtype_val.pow 2).mul
        ((continuous_J (continuous_ext f)).comp continuous_subtype_val))⟩

theorem Tmap_apply (c : ℝ) (f : Sp) (x : Icc (0 : ℝ) (1 / 5)) :
    Tmap c f x = c + (x : ℝ) ^ 2 * J (ext f) x := rfl

theorem sq_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) : x ^ 2 ≤ 1 / 25 := by
  nlinarith [hx.1, hx.2]

theorem contracting (c : ℝ) : ContractingWith (13 / 25) (Tmap c) := by
  constructor
  · exact NNReal.coe_lt_coe.1 (by norm_num)
  · refine LipschitzWith.of_dist_le_mul fun f h => ?_
    rw [BoundedContinuousFunction.dist_le (by positivity)]
    intro x
    rw [Tmap_apply, Tmap_apply, Real.dist_eq]
    have hJ := J_sub_le (continuous_ext f) (continuous_ext h) (dist_ext f h) x
    have e : (c + (x : ℝ) ^ 2 * J (ext f) x) - (c + (x : ℝ) ^ 2 * J (ext h) x)
        = (x : ℝ) ^ 2 * (J (ext f) x - J (ext h) x) := by ring
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hx2 := sq_le x.2
    have hc : ((13 / 25 : NNReal) : ℝ) = 13 / 25 := by norm_num
    rw [hc]
    nlinarith [abs_nonneg (J (ext f) x - J (ext h) x), dist_nonneg (x := f) (y := h),
      sq_nonneg (x : ℝ)]

/-- The fixed point. -/
noncomputable def θs (c : ℝ) : Sp := ContractingWith.fixedPoint (Tmap c) (contracting c)

/-- The solution on [0, 1/5] (extended constantly outside). -/
noncomputable def θL (c : ℝ) : ℝ → ℝ := ext (θs c)

theorem continuous_θL (c : ℝ) : Continuous (θL c) := continuous_ext _

theorem θL_eq (c : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) :
    θL c x = c + x ^ 2 * J (θL c) x := by
  have hfix : Tmap c (θs c) = θs c := (contracting c).fixedPoint_isFixedPt
  have h1 := DFunLike.congr_fun hfix ⟨x, hx⟩
  unfold θL ext
  rw [IccExtend_of_mem h15 _ hx, ← h1]
  rfl

theorem θL_zero (c : ℝ) : θL c 0 = c := by
  rw [θL_eq c ⟨le_rfl, h15⟩]; ring

theorem θL_near (c : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) : |θL c x - c| ≤ 12 / 25 := by
  rw [θL_eq c hx]
  have hJ := abs_J_le (continuous_θL c) x
  have hx2 := sq_le hx
  rw [show c + x ^ 2 * J (θL c) x - c = x ^ 2 * J (θL c) x by ring, abs_mul,
    abs_of_nonneg (sq_nonneg _)]
  nlinarith [abs_nonneg (J (θL c) x), sq_nonneg x]

theorem θL_ge {c : ℝ} (hc : c ∈ Icc (2.2 : ℝ) 2.21) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) :
    3 / 2 ≤ θL c x ∧ θL c x ≤ 3 := by
  have h := abs_le.1 (θL_near c hx)
  have := hc.1; have := hc.2
  constructor <;> norm_num at * <;> linarith [h.1, h.2]

theorem mul_mem {x u : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) (hu : u ∈ Icc (0 : ℝ) 1) :
    x * u ∈ Icc (0 : ℝ) (1 / 5) :=
  ⟨mul_nonneg hx.1 hu.1, by nlinarith [hx.1, hx.2, hu.1, hu.2]⟩

theorem J_nonpos {c : ℝ} (hc : c ∈ Icc (2.2 : ℝ) 2.21) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) :
    J (θL c) x ≤ 0 := by
  unfold J
  have hle := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((cont_kernel (continuous_θL c) x).intervalIntegrable 0 1)
    (intervalIntegrable_const (c := (0 : ℝ)))
    (fun u hu => by
      have hb := θL_ge hc (mul_mem hx hu)
      have hg := g_le_neg_one hb.1 hb.2
      show Real.negMulLog u * g (θL c (x * u)) ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (w_nonneg hu) (by linarith))
  simpa using hle

theorem θL_bounds {c : ℝ} (hc : c ∈ Icc (2.2 : ℝ) 2.21) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) :
    3 / 2 ≤ θL c x ∧ θL c x ≤ 5 / 2 := by
  refine ⟨(θL_ge hc hx).1, ?_⟩
  rw [θL_eq c hx]
  have := J_nonpos hc hx
  have := hc.2
  nlinarith [sq_nonneg x]

/-- g ∘ θL. -/
noncomputable def G (c s : ℝ) : ℝ := g (θL c s)

theorem continuous_G (c : ℝ) : Continuous (G c) := continuous_g.comp (continuous_θL c)

theorem G_eq {c : ℝ} (hc : c ∈ Icc (2.2 : ℝ) 2.21) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) :
    G c x = θL c x - θL c x ^ 3 := by
  have hb := θL_ge hc hx
  unfold G g; rw [cl_of_abs_le (abs_le.2 ⟨by linarith [hb.1], hb.2⟩)]

/-- The derivative: φ(x) = x ∫₀¹ u g(θ(xu)) du. -/
noncomputable def φL (c x : ℝ) : ℝ := x * ∫ u in (0 : ℝ)..1, u * G c (x * u)

theorem cont_uG (c x : ℝ) : Continuous fun u : ℝ => u * G c (x * u) :=
  continuous_id.mul ((continuous_G c).comp (continuous_const.mul continuous_id))

theorem continuous_φL (c : ℝ) : Continuous (φL c) := by
  unfold φL
  refine continuous_id.mul ?_
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (by
    have : Continuous fun p : ℝ × ℝ => p.2 * G c (p.1 * p.2) :=
      continuous_snd.mul ((continuous_G c).comp (continuous_fst.mul continuous_snd))
    exact this)

theorem φL_zero (c : ℝ) : φL c 0 = 0 := by simp [φL]

theorem abs_φL_le (c : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) : |φL c x| ≤ 3 := by
  unfold φL
  rw [abs_mul, abs_of_nonneg hx.1]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun u => u * G c (x * u)) (g := fun u => u * 24) zero_le_one
    (ae_of_all _ fun u hu => by
      have hu' := mem_of_uIoc hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu'.1]
      exact mul_le_mul_of_nonneg_left (abs_g_le _) hu'.1)
    ((show Continuous fun u : ℝ => u * 24 by fun_prop).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, int_u, Real.norm_eq_abs] at hb
  have hx2 := hx.2
  nlinarith [abs_nonneg (∫ u in (0 : ℝ)..1, u * G c (x * u)), hx.1]

theorem φL_neg {c : ℝ} (hc : c ∈ Icc (2.2 : ℝ) 2.21) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 5)) :
    φL c x < 0 := by
  have hx' : x ∈ Icc (0 : ℝ) (1 / 5) := Ioc_subset_Icc_self hx
  have hle := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((cont_uG c x).intervalIntegrable 0 1)
    ((show Continuous fun u : ℝ => u * (-1) by fun_prop).intervalIntegrable 0 1)
    (fun u hu => by
      have hb := θL_ge hc (mul_mem hx' hu)
      have hg := g_le_neg_one hb.1 hb.2
      show u * G c (x * u) ≤ u * (-1)
      exact mul_le_mul_of_nonneg_left hg hu.1)
  rw [intervalIntegral.integral_mul_const, int_u] at hle
  unfold φL
  nlinarith [hx.1]

/-- ∫₀^x s G. -/
noncomputable def A (c x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, s * G c s

/-- ∫₀^x s log s G. -/
noncomputable def B (c x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, s * Real.log s * G c s

theorem cont_sG (c : ℝ) : Continuous fun s => s * G c s := continuous_id.mul (continuous_G c)
theorem cont_slG (c : ℝ) : Continuous fun s => s * Real.log s * G c s :=
  Real.continuous_mul_log.mul (continuous_G c)

theorem hasDerivAt_A (c x : ℝ) : HasDerivAt (A c) (x * G c x) x :=
  ((cont_sG c).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem hasDerivAt_B (c x : ℝ) : HasDerivAt (B c) (x * Real.log x * G c x) x :=
  ((cont_slG c).integral_hasStrictDerivAt 0 x).hasDerivAt

/-- Substitution s = xu in J. -/
theorem J_subst (c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    x ^ 2 * J (θL c) x = Real.log x * A c x - B c x := by
  unfold J
  have key := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun s => x⁻¹ * Real.log x * (s * G c s) - x⁻¹ * (s * Real.log s * G c s)) hx
  rw [mul_zero, mul_one] at key
  have e1 : (∫ u in (0 : ℝ)..1, Real.negMulLog u * g (θL c (x * u)))
      = ∫ u in (0 : ℝ)..1, (x⁻¹ * Real.log x * (x * u * G c (x * u))
          - x⁻¹ * (x * u * Real.log (x * u) * G c (x * u))) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [G, Real.negMulLog]
    rcases eq_or_ne u 0 with hu | hu
    · subst hu; simp
    · rw [Real.log_mul hx hu]; field_simp; ring
  rw [e1, key,
    intervalIntegral.integral_sub (((cont_sG c).intervalIntegrable _ _).const_mul _)
      (((cont_slG c).intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold A B
  simp only [smul_eq_mul]
  field_simp

/-- Substitution s = xu in φ. -/
theorem φL_subst (c : ℝ) {x : ℝ} (hx : x ≠ 0) : φL c x = x⁻¹ * A c x := by
  unfold φL
  have key := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun s => x⁻¹ * (s * G c s)) hx
  rw [mul_zero, mul_one] at key
  have e1 : (∫ u in (0 : ℝ)..1, u * G c (x * u))
      = ∫ u in (0 : ℝ)..1, x⁻¹ * (x * u * G c (x * u)) :=
    intervalIntegral.integral_congr fun u _ => by field_simp
  rw [e1, key, intervalIntegral.integral_const_mul]
  unfold A
  simp only [smul_eq_mul]
  field_simp

theorem pos_mem_nhds {x : ℝ} (hx : 0 < x) :
    Ioc (0 : ℝ) (1 / 5) ∈ 𝓝[Icc (0 : ℝ) (1 / 5)] x :=
  mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, hx, fun _y hy => ⟨hy.1, hy.2.2⟩⟩

theorem hasDerivAt_mul_cont {K : ℝ → ℝ} (hK : ContinuousAt K 0) :
    HasDerivAt (fun ε => ε * K ε) (K 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine (hK.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
  field_simp

theorem deriv_θL (c : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) :
    HasDerivWithinAt (θL c) (φL c x) (Icc 0 (1 / 5)) x := by
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · subst h0
    have hK : ContinuousAt (fun y => y * J (θL c) y) 0 :=
      (continuous_id.mul (continuous_J (continuous_θL c))).continuousAt
    have hd := (hasDerivAt_const (0 : ℝ) c).add (hasDerivAt_mul_cont hK)
    rw [φL_zero]
    refine (hd.hasDerivWithinAt.congr (fun y hy => ?_) ?_).congr_deriv (by simp)
    · simp only [Pi.add_apply]; rw [θL_eq c hy]; ring
    · simp only [Pi.add_apply]; rw [θL_eq c hx]; ring
  · have hxne : x ≠ 0 := hpos.ne'
    have hd := (hasDerivAt_const x c).add
      (((Real.hasDerivAt_log hxne).mul (hasDerivAt_A c x)).sub (hasDerivAt_B c x))
    have hval : 0 + (x⁻¹ * A c x + Real.log x * (x * G c x) - x * Real.log x * G c x)
        = φL c x := by
      rw [φL_subst c hxne]; ring
    rw [← hval]
    refine (hd.hasDerivWithinAt.congr (s := Ioc 0 (1 / 5)) (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin
      (pos_mem_nhds hpos)
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      rw [θL_eq c (Ioc_subset_Icc_self hy), J_subst c hy.1.ne']
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      rw [θL_eq c hx, J_subst c hxne]

theorem deriv_φL {c : ℝ} (hc : c ∈ Icc (2.2 : ℝ) 2.21) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 5)) :
    HasDerivWithinAt (φL c) (-(1 / x * φL c x) + θL c x - θL c x ^ 3) (Icc 0 (1 / 5)) x := by
  have hxne : x ≠ 0 := hx.1.ne'
  have hd := (hasDerivAt_inv hxne).mul (hasDerivAt_A c x)
  have hG := G_eq hc (Ioc_subset_Icc_self hx)
  have hval : -(x ^ 2)⁻¹ * A c x + x⁻¹ * (x * G c x)
      = -(1 / x * φL c x) + θL c x - θL c x ^ 3 := by
    rw [φL_subst c hxne, hG]; field_simp; ring
  rw [← hval]
  refine (hd.hasDerivWithinAt.congr (s := Ioc 0 (1 / 5)) (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin
    (pos_mem_nhds hx.1)
  · simp only [Pi.mul_apply]; rw [φL_subst c hy.1.ne']
  · simp only [Pi.mul_apply]; rw [φL_subst c hxne]

/-- Lipschitz dependence of the fixed point on c. -/
theorem θL_lip (c c' y : ℝ) : |θL c y - θL c' y| ≤ 25 / 12 * |c - c'| := by
  have hd := (contracting c).dist_fixedPoint_fixedPoint_of_dist_le' (Tmap c')
    (contracting c).fixedPoint_isFixedPt (contracting c').fixedPoint_isFixedPt
    (C := |c - c'|) (fun z => by
      rw [BoundedContinuousFunction.dist_le (abs_nonneg _)]
      intro x
      rw [Tmap_apply, Tmap_apply, Real.dist_eq]
      exact le_of_eq (by ring_nf))
  have hc : ((13 / 25 : NNReal) : ℝ) = 13 / 25 := by norm_num
  rw [hc] at hd
  have h1 := dist_ext (θs c) (θs c') y
  have h2 : dist (θs c) (θs c') ≤ 25 / 12 * |c - c'| := by
    have : |c - c'| / (1 - 13 / 25) = 25 / 12 * |c - c'| := by ring
    rw [← this]; exact hd
  exact h1.trans h2

theorem φL_lip (c c' : ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 / 5)) :
    |φL c x - φL c' x| ≤ 6 * |c - c'| := by
  unfold φL
  have i1 := (cont_uG c x).intervalIntegrable (μ := volume) 0 1
  have i2 := (cont_uG c' x).intervalIntegrable (μ := volume) 0 1
  rw [← mul_sub, ← intervalIntegral.integral_sub i1 i2, abs_mul, abs_of_nonneg hx.1]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
    (f := fun u => u * G c (x * u) - u * G c' (x * u))
    (g := fun u => u * (26 * (25 / 12 * |c - c'|))) zero_le_one
    (ae_of_all _ fun u hu => by
      have hu' := mem_of_uIoc hu
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hu'.1]
      refine mul_le_mul_of_nonneg_left ((g_sub _ _).trans ?_) hu'.1
      exact mul_le_mul_of_nonneg_left (θL_lip c c' _) (by norm_num))
    ((show Continuous fun u : ℝ => u * (26 * (25 / 12 * |c - c'|)) by fun_prop).intervalIntegrable
      _ _)
  rw [intervalIntegral.integral_mul_const, int_u, Real.norm_eq_abs] at hb
  have hx2 := hx.2
  nlinarith [abs_nonneg (∫ u in (0 : ℝ)..1, (u * G c (x * u) - u * G c' (x * u))), hx.1,
    abs_nonneg (c - c')]

/-- The left piece of the Townes existence proof. -/
theorem left : ∃ Θ Φ : ℝ → ℝ → ℝ,
    (∀ c ∈ Icc (2.2 : ℝ) 2.21,
      Θ c 0 = c ∧ Φ c 0 = 0 ∧
      (∀ x ∈ Icc (0 : ℝ) (1 / 5), HasDerivWithinAt (Θ c) (Φ c x) (Icc 0 (1 / 5)) x) ∧
      ContinuousOn (Φ c) (Icc 0 (1 / 5)) ∧
      (∀ x ∈ Ioc (0 : ℝ) (1 / 5),
        HasDerivWithinAt (Φ c) (-(1 / x * Φ c x) + Θ c x - Θ c x ^ 3) (Icc 0 (1 / 5)) x) ∧
      (∀ x ∈ Icc (0 : ℝ) (1 / 5), 3 / 2 ≤ Θ c x ∧ Θ c x ≤ 5 / 2) ∧
      (∀ x ∈ Ioc (0 : ℝ) (1 / 5), Φ c x < 0) ∧
      (∀ x ∈ Icc (0 : ℝ) (1 / 5), |Φ c x| ≤ 3)) ∧
    ∃ K : ℝ, ∀ c ∈ Icc (2.2 : ℝ) 2.21, ∀ c' ∈ Icc (2.2 : ℝ) 2.21, ∀ x ∈ Icc (0 : ℝ) (1 / 5),
      |Θ c x - Θ c' x| ≤ K * |c - c'| ∧ |Φ c x - Φ c' x| ≤ K * |c - c'| := by
  refine ⟨θL, φL, fun c hc => ⟨θL_zero c, φL_zero c, fun x hx => deriv_θL c hx,
    (continuous_φL c).continuousOn, fun x hx => deriv_φL hc hx, fun x hx => θL_bounds hc hx,
    fun x hx => φL_neg hc hx, fun x hx => abs_φL_le c hx⟩, 6, fun c _ c' _ x hx => ⟨?_, φL_lip c c' hx⟩⟩
  exact (θL_lip c c' x).trans (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

end Checked.Townes.TExLeft
