import Mathlib
import Checked.Math.Gelfand
import Checked.Math.GExistsRight

/-! Laplacian of a radial function `y ↦ f ‖y‖` away from the origin, in a finite-dimensional real
inner product space of dimension `n`: `Δ (f ∘ ‖·‖) x = f''(r) + (n - 1) / r · f'(r)`, `r = ‖x‖`. -/

namespace RadialLaplacian
open InnerProductSpace Filter Topology Laplacian
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_norm {x : E} (hx : x ≠ 0) :
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

theorem laplacian_radial {f f' : ℝ → ℝ} {f'' : ℝ} {x : E} (hx : x ≠ 0)
    (hf : ∀ᶠ ρ in 𝓝 ‖x‖, HasDerivAt f (f' ρ) ρ) (hf' : HasDerivAt f' f'' ‖x‖) :
    Δ (fun y : E => f ‖y‖) x =
      f'' + ((Module.finrank ℝ E : ℝ) - 1) / ‖x‖ * f' ‖x‖ := by
  set r := ‖x‖ with hr
  have hr0 : r ≠ 0 := norm_ne_zero_iff.2 hx
  -- first derivative near x
  have hev : ∀ᶠ y in 𝓝 x, y ≠ 0 ∧ HasDerivAt f (f' ‖y‖) ‖y‖ :=
    (eventually_ne_nhds hx).and ((continuous_norm.tendsto x).eventually hf)
  set h : E → E →L[ℝ] ℝ := fun y => (f' ‖y‖ * ‖y‖⁻¹) • innerSL ℝ y with hh
  have hD : fderiv ℝ (fun y : E => f ‖y‖) =ᶠ[𝓝 x] h := by
    filter_upwards [hev] with y hy
    have := hy.2.comp_hasFDerivAt y (hasFDerivAt_norm hy.1)
    rw [Function.comp_def] at this
    rw [this.fderiv, hh]
    simp only [smul_smul]
  -- derivative of the scalar factor
  have hn := hasFDerivAt_norm hx
  have ha1 : HasFDerivAt (fun y : E => f' ‖y‖) (f'' • (r⁻¹ • innerSL ℝ x)) x :=
    hf'.comp_hasFDerivAt x hn
  have ha2 : HasFDerivAt (fun y : E => ‖y‖⁻¹) ((-(r ^ 2)⁻¹) • (r⁻¹ • innerSL ℝ x)) x :=
    (hasDerivAt_inv hr0).comp_hasFDerivAt x hn
  have ha := ha1.fun_mul ha2
  have hL : HasFDerivAt (fun y : E => innerSL ℝ y) (innerSL ℝ) x := (innerSL ℝ).hasFDerivAt
  have hH := ha.fun_smul hL
  have key : ∀ v : E, fderiv ℝ (fderiv ℝ (fun y : E => f ‖y‖)) x v v =
      f' r * r⁻¹ * ⟪v, v⟫ + (r⁻¹ * (f'' * (r⁻¹ * ⟪x, v⟫)) +
        f' r * (-(r ^ 2)⁻¹ * (r⁻¹ * ⟪x, v⟫))) * ⟪x, v⟫ := by
    intro v
    rw [hD.fderiv_eq, hh, hH.fderiv]
    simp [innerSL_apply_apply, smul_eq_mul, hr]
    have hv : (innerSL ℝ) v v = ‖v‖ ^ 2 := by
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    rw [hv]
    ring
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, key]
  set b := stdOrthonormalBasis ℝ E
  have hvv : ∀ i, ⟪b i, b i⟫ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have hsq := b.sum_sq_inner_left x
  have hcard : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).card = Module.finrank ℝ E := by
    simp
  simp only [hvv]
  have e2 : ∀ i, (f' r * r⁻¹ * 1 + (r⁻¹ * (f'' * (r⁻¹ * ⟪x, b i⟫)) +
        f' r * (-(r ^ 2)⁻¹ * (r⁻¹ * ⟪x, b i⟫))) * ⟪x, b i⟫) =
      f' r * r⁻¹ + (f'' * r⁻¹ ^ 2 - f' r * r⁻¹ ^ 3) * ⟪x, b i⟫ ^ 2 := fun i => by ring
  simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hsq, hcard,
    nsmul_eq_mul]
  rw [← hr]
  field_simp
  ring

end RadialLaplacian


/-! Continuation of solutions of w'' + (2/s) w' + e^w = 0 from any start a > 0 with w(a) ≤ 0,
w'(a) ≤ 0 (the run-1228Z right piece, which starts at 1/2, generalised to any a > 0). -/

namespace GelfandCont
open Set Checked.Math.GExistsRight

theorem lipF' {Q T a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a T) :
    LipschitzWith (Real.toNNReal (1 / a ^ 2 + T ^ 2)) (F Q t) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hK : (0 : ℝ) ≤ 1 / a ^ 2 + T ^ 2 := by positivity
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [Real.coe_toNNReal _ hK]
  simp only [F, Prod.dist_eq, Real.dist_eq]
  have hd1 : |p.1 - q.1| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_left _ _
  have hd2 : |p.2 - q.2| ≤ max |p.1 - q.1| |p.2 - q.2| := le_max_right _ _
  have hm0 : 0 ≤ max |p.1 - q.1| |p.2 - q.2| := (abs_nonneg _).trans hd1
  have ht2 : a ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
  have htT : t ^ 2 ≤ T ^ 2 := by
    have := ht.2; nlinarith [ht.1]
  have ha2 : 0 < a ^ 2 := by positivity
  refine max_le ?_ ?_
  · rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    have := cl_sub Q p.2 q.2
    have h1 : 1 ≤ 1 / a ^ 2 * t ^ 2 := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha2]; linarith
    have b : 0 ≤ T ^ 2 * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg T) hm0) (sq_nonneg t)
    have h4 : |p.2 - q.2| ≤ (1 / a ^ 2 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by
      have e : (1 / a ^ 2 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 =
          (1 / a ^ 2 * t ^ 2) * max |p.1 - q.1| |p.2 - q.2| +
            T ^ 2 * max |p.1 - q.1| |p.2 - q.2| * t ^ 2 := by ring
      rw [e]; nlinarith
    linarith
  · have e : -(t ^ 2 * Real.exp (min p.1 0)) - -(t ^ 2 * Real.exp (min q.1 0)) =
        -(t ^ 2 * (Real.exp (min p.1 0) - Real.exp (min q.1 0))) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg t)]
    have h1 := exp_sub_le_of_le (min_le_right p.1 0) (min_le_right q.1 0)
    rw [Real.exp_zero, one_mul] at h1
    have h2 : |min p.1 0 - min q.1 0| ≤ |p.1 - q.1| := abs_min_sub_min_le_max _ _ _ _ |>.trans
      (max_le le_rfl (by simp))
    have h3 : |Real.exp (min p.1 0) - Real.exp (min q.1 0)| ≤ max |p.1 - q.1| |p.2 - q.2| :=
      (h1.trans h2).trans hd1
    have h5 : 0 ≤ 1 / a ^ 2 * max |p.1 - q.1| |p.2 - q.2| := by positivity
    calc t ^ 2 * |Real.exp (min p.1 0) - Real.exp (min q.1 0)|
        ≤ T ^ 2 * max |p.1 - q.1| |p.2 - q.2| :=
          mul_le_mul htT h3 (abs_nonneg _) (sq_nonneg _)
      _ ≤ (1 / a ^ 2 + T ^ 2) * max |p.1 - q.1| |p.2 - q.2| := by nlinarith

theorem normF' {Q T a t : ℝ} (ha : 0 < a) (hQ : 0 ≤ Q) (ht : t ∈ Icc a T) (p : ℝ × ℝ) :
    ‖F Q t p‖ ≤ Q / a ^ 2 + T ^ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht2 : a ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
  have htT : t ^ 2 ≤ T ^ 2 := by
    have := ht.2; nlinarith [ht.1]
  have ha2 : 0 < a ^ 2 := by positivity
  simp only [F, Prod.norm_def, Real.norm_eq_abs]
  have hc := abs_cl_le hQ p.2
  refine max_le ?_ ?_
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2)]
    have h1 : |cl Q p.2| / t ^ 2 ≤ Q / a ^ 2 :=
      div_le_div₀ hQ hc ha2 ht2
    have : 0 ≤ T ^ 2 := sq_nonneg T
    linarith
  · rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_pos (Real.exp_pos _)]
    have : Real.exp (min p.1 0) ≤ 1 := Real.exp_le_one_iff.2 (min_le_right _ _)
    have : 0 ≤ Q / a ^ 2 := by positivity
    nlinarith [Real.exp_pos (min p.1 0)]

theorem contF' {Q T a : ℝ} (ha : 0 < a) (x : ℝ × ℝ) :
    ContinuousOn (fun t => F Q t x) (Icc a T) := by
  unfold F
  refine ContinuousOn.prodMk ?_ ?_
  · exact continuousOn_const.div (continuousOn_id.pow 2) fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity
  · exact ((continuousOn_id.pow 2).mul continuousOn_const).neg

theorem exists_from (a T w₀ φ₀ : ℝ) (ha : 0 < a) (hT : a ≤ T) (hw₀ : w₀ ≤ 0) (hφ₀ : φ₀ ≤ 0) :
    ∃ w φ : ℝ → ℝ, w a = w₀ ∧ φ a = φ₀ ∧
      ∀ t ∈ Icc a T, HasDerivWithinAt w (φ t) (Icc a T) t ∧
        HasDerivWithinAt φ (-(2 / t * φ t) - Real.exp (w t)) (Icc a T) t := by
  set q₀ : ℝ := a ^ 2 * φ₀ with hq₀
  have hq₀n : q₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hφ₀
  set Q : ℝ := T ^ 3 - q₀ with hQ
  have hT0 : 0 < T := by linarith
  have hQ0 : 0 ≤ Q := by have := pow_pos hT0 3; linarith
  set L : ℝ := Q / a ^ 2 + T ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  have hPL : IsPicardLindelof (F Q) (tmin := a) (tmax := T)
      ⟨a, le_rfl, hT⟩ (w₀, q₀) (Real.toNNReal (L * T)) 0 (Real.toNNReal L)
      (Real.toNNReal (1 / a ^ 2 + T ^ 2)) :=
    { lipschitzOnWith := fun t ht => (lipF' ha ht).lipschitzOnWith
      continuousOn := fun x _ => contF' ha x
      norm_le := fun t ht p _ => by
        rw [Real.coe_toNNReal _ hL0]; exact normF' ha hQ0 ht p
      mul_max_le := by
        rw [Real.coe_toNNReal _ hL0, NNReal.coe_zero, sub_zero,
          Real.coe_toNNReal _ (by positivity)]
        simp only
        rw [sub_self, max_eq_left (by linarith)]
        nlinarith }
  obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  simp only at h0
  set w : ℝ → ℝ := fun t => (α t).1 with hw
  set q : ℝ → ℝ := fun t => (α t).2 with hq
  have hw0 : w a = w₀ := by simp only [hw, h0]
  have hq0 : q a = q₀ := by simp only [hq, h0]
  have dw : ∀ t ∈ Icc a T, HasDerivWithinAt w (cl Q (q t) / t ^ 2) (Icc a T) t :=
    fun t ht => by have := fst_derivW (hα t ht); simpa [F] using this
  have dq : ∀ t ∈ Icc a T,
      HasDerivWithinAt q (-(t ^ 2 * Real.exp (min (w t) 0))) (Icc a T) t :=
    fun t ht => by have := snd_derivW (hα t ht); simpa [F] using this
  have cq : ContinuousOn q (Icc a T) := fun t ht => (dq t ht).continuousWithinAt
  have cw : ContinuousOn w (Icc a T) := fun t ht => (dw t ht).continuousWithinAt
  have qanti : AntitoneOn q (Icc a T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) cq
      (fun t ht => ((dq t (interior_subset ht)).mono interior_subset))
    intro t _
    have := Real.exp_pos (min (w t) 0)
    nlinarith [sq_nonneg t]
  have qmono : MonotoneOn (fun t => q t + T ^ 2 * t) (Icc a T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (cq.add (continuousOn_const.mul continuousOn_id))
      (fun t ht => (((dq t (interior_subset ht)).add
        ((hasDerivAt_id t).const_mul (T ^ 2)).hasDerivWithinAt).mono interior_subset))
    intro t ht
    rw [interior_Icc] at ht
    have h1 : Real.exp (min (w t) 0) ≤ 1 := Real.exp_le_one_iff.2 (min_le_right _ _)
    have h2 : t ^ 2 ≤ T ^ 2 := by nlinarith [ht.1, ht.2]
    have h3 := Real.exp_pos (min (w t) 0)
    simp only [mul_one]
    nlinarith [sq_nonneg t]
  have hm : a ∈ Icc a T := ⟨le_rfl, hT⟩
  have qle : ∀ t ∈ Icc a T, q t ≤ q₀ := fun t ht => by
    rw [← hq0]; exact qanti hm ht ht.1
  have qge : ∀ t ∈ Icc a T, q₀ - T ^ 3 ≤ q t := fun t ht => by
    have h := qmono hm ht ht.1
    simp only [hq0] at h
    have h1 : T ^ 2 * t ≤ T ^ 3 := by
      have := ht.2; nlinarith [sq_nonneg T]
    have h2 : 0 ≤ T ^ 2 * a := by positivity
    nlinarith [sq_nonneg T]
  have qin : ∀ t ∈ Icc a T, |q t| ≤ Q := fun t ht => by
    have h1 := qle t ht
    have h2 := qge t ht
    have h3 := pow_pos hT0 3
    rw [abs_le]; constructor <;> linarith
  have hqcl : ∀ t ∈ Icc a T, cl Q (q t) = q t := fun t ht => cl_of_abs_le (qin t ht)
  have wanti : AntitoneOn w (Icc a T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) cw
      (fun t ht => ((dw t (interior_subset ht)).mono interior_subset))
    intro t ht
    have ht' := interior_subset ht
    rw [hqcl t ht']
    have : q t ≤ 0 := (qle t ht').trans hq₀n
    exact div_nonpos_of_nonpos_of_nonneg this (sq_nonneg t)
  have wle : ∀ t ∈ Icc a T, w t ≤ 0 := fun t ht => by
    have := wanti hm ht ht.1
    rw [hw0] at this; linarith
  refine ⟨w, fun t => q t / t ^ 2, hw0, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [hq0, hq₀]; field_simp
  · have := dw t ht
    rwa [hqcl t ht] at this
  · have ht0 : t ≠ 0 := (lt_of_lt_of_le ha ht.1).ne'
    have h := (dq t ht).div ((hasDerivAt_pow 2 t).hasDerivWithinAt) (pow_ne_zero 2 ht0)
    rw [min_eq_left (wle t ht)] at h
    convert h using 1
    field_simp
    ring

end GelfandCont

namespace GelfandPDE
open Set Filter Topology InnerProductSpace Laplacian

/-- Gluing two one-sided derivatives at an interior point `c` (the run-1228Z `glue`, at any `c`). -/
theorem glue_at {c S : ℝ} {fL fR d : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc (0 : ℝ) S)
    (hc0 : 0 ≤ c) (hcS : c ≤ S) (heq : fL c = fR c)
    (hL : x ≤ c → HasDerivWithinAt fL (d x) (Icc 0 c) x)
    (hR : c ≤ x → HasDerivWithinAt fR (d x) (Icc c S) x) :
    HasDerivWithinAt (fun y => if y ≤ c then fL y else fR y) (d x) (Icc 0 S) x := by
  set F : ℝ → ℝ := fun y => if y ≤ c then fL y else fR y with hF
  have eL : EqOn F fL (Icc 0 c) := fun y hy => by rw [hF]; exact if_pos hy.2
  have eR : EqOn F fR (Icc c S) := fun y hy => by
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; rw [hF]; exact (if_pos le_rfl).trans heq
    · rw [hF]; exact if_neg (not_le.2 h)
  have hL' : x ≤ c → HasDerivWithinAt F (d x) (Icc 0 c) x := fun h =>
    (hL h).congr eL (eL ⟨hx.1, h⟩)
  have hR' : c ≤ x → HasDerivWithinAt F (d x) (Icc c S) x := fun h =>
    (hR h).congr eR (eR ⟨h, hx.2⟩)
  rcases lt_trichotomy x c with h | h | h
  · refine (hL' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio c, isOpen_Iio, h, fun y hy => ⟨hy.2.1, le_of_lt hy.1⟩⟩)
  · have hu : Icc (0 : ℝ) S = Icc 0 c ∪ Icc c S := (Icc_union_Icc_eq_Icc hc0 hcS).symm
    rw [hu]
    exact (hL' h.le).union (hR' h.ge)
  · refine (hR' h.le).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, h, fun y hy => ⟨le_of_lt hy.1, hy.2.2⟩⟩)

/-- ODE form of the bound: a solution `f` of `f'' + (2/r) f' + λ e^f = 0` on (0, 1), twice
differentiable on (−1, 1) with `f'(0) = 0`, continuous at 1 from the left with `f(1) = 0`, has
`λ ≤ 3.321992119`. -/
theorem ode_bound (lam : ℝ) (hlam : 0 < lam) (f f' f'' : ℝ → ℝ)
    (hf : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f' r) r)
    (hf' : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt f' (f'' r) r)
    (hf'0 : f' 0 = 0)
    (hode : ∀ r ∈ Ioo (0 : ℝ) 1, f'' r + 2 / r * f' r + lam * Real.exp (f r) = 0)
    (hcont : ContinuousWithinAt f (Icc 0 1) 1) (h1 : f 1 = 0) :
    lam ≤ 3.321992119 := by
  set α := f 0 with hα
  set k := Real.sqrt lam * Real.exp (α / 2) with hk
  have hk0 : 0 < k := mul_pos (Real.sqrt_pos.2 hlam) (Real.exp_pos _)
  have hkne : k ≠ 0 := hk0.ne'
  have hk2 : k ^ 2 = lam * Real.exp α := by
    rw [hk, mul_pow, Real.sq_sqrt hlam.le, sq, ← Real.exp_add, add_halves]
  set w : ℝ → ℝ := fun s => f (s / k) - α with hw
  set φ : ℝ → ℝ := fun s => f' (s / k) / k with hφ
  have mem : ∀ s ∈ Ioo (-k) k, s / k ∈ Ioo (-1 : ℝ) 1 := fun s hs =>
    ⟨by rw [lt_div_iff₀ hk0]; linarith [hs.1], by rw [div_lt_one hk0]; exact hs.2⟩
  have dw : ∀ s ∈ Ioo (-k) k, HasDerivAt w (φ s) s := by
    intro s hs
    have h := ((hf _ (mem s hs)).comp s ((hasDerivAt_id s).div_const k)).sub_const α
    convert h using 1
    · rfl
    · simp only [hφ]; ring
  have dφ : ∀ s ∈ Ioo (-k) k, HasDerivAt φ (f'' (s / k) / k ^ 2) s := by
    intro s hs
    have h := ((hf' _ (mem s hs)).comp s ((hasDerivAt_id s).div_const k)).div_const k
    convert h using 1
    · rfl
    · ring
  have hode' : ∀ s ∈ Ioo 0 k, f'' (s / k) / k ^ 2 = -(2 / s * φ s) - Real.exp (w s) := by
    intro s hs
    have hr : s / k ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hs.1 hk0, (div_lt_one hk0).2 hs.2⟩
    have h := hode _ hr
    have hs0 : s ≠ 0 := hs.1.ne'
    have e1 : Real.exp (w s) = Real.exp (f (s / k)) / Real.exp α := by
      simp only [hw, Real.exp_sub]
    rw [e1, hφ]
    have hlam' : lam = k ^ 2 / Real.exp α := by
      rw [hk2]; field_simp
    rw [hlam'] at h
    field_simp at h ⊢
    linear_combination h
  -- sign facts on [0, k)
  have hsub : Ico 0 k ⊆ Ioo (-k) k := fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have cφ : ContinuousOn φ (Ico 0 k) := fun s hs =>
    (dφ s (hsub hs)).continuousAt.continuousWithinAt
  have cw : ContinuousOn w (Ico 0 k) := fun s hs =>
    (dw s (hsub hs)).continuousAt.continuousWithinAt
  set q : ℝ → ℝ := fun s => s ^ 2 * φ s with hq
  have dq : ∀ s ∈ Ioo 0 k, HasDerivAt q (-(s ^ 2 * Real.exp (w s))) s := by
    intro s hs
    have h := ((hasDerivAt_pow 2 s).mul (dφ s ⟨by linarith [hs.1], hs.2⟩))
    rw [hode' s hs] at h
    convert h using 1
    have : s ≠ 0 := hs.1.ne'
    field_simp
    ring
  have cq : ContinuousOn q (Ico 0 k) := (continuousOn_id.pow 2).mul cφ
  have qanti : AntitoneOn q (Ico 0 k) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 k) cq
    · intro s hs
      rw [interior_Ico] at hs
      exact (dq s hs).hasDerivWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      have := Real.exp_pos (w s)
      nlinarith [sq_nonneg s]
  have h0k : (0 : ℝ) ∈ Ico 0 k := ⟨le_rfl, hk0⟩
  have φ0 : φ 0 = 0 := by simp [hφ, hf'0]
  have φle : ∀ s ∈ Ico 0 k, φ s ≤ 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, φ0]
    · have hq0 : q s ≤ 0 := by
        have := qanti h0k hs hs.1
        simpa [hq, φ0] using this
      have hs2 : 0 < s ^ 2 := by positivity
      simp only [hq] at hq0
      by_contra hc
      push_neg at hc
      have := mul_pos hs2 hc
      linarith
  have wanti : AntitoneOn w (Ico 0 k) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 k) cw
    · intro s hs
      rw [interior_Ico] at hs
      exact (dw s ⟨by linarith [hs.1], hs.2⟩).hasDerivWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      exact φle s ⟨hs.1.le, hs.2⟩
  have w0 : w 0 = 0 := by simp [hw, hα]
  have wle : ∀ s ∈ Ico 0 k, w s ≤ 0 := fun s hs => by
    have := wanti h0k hs hs.1
    rw [w0] at this; exact this
  -- every c in (0, k) gives c² e^{w c} ≤ the certified bound
  have key : ∀ c ∈ Ioo 0 k, c ^ 2 * Real.exp (w c) ≤ 3.321992119 := by
    intro c hc
    set T : ℝ := 41 / 10 + k with hT
    have hcT : c ≤ T := by linarith [hc.2]
    have hcI : c ∈ Ico 0 k := ⟨hc.1.le, hc.2⟩
    obtain ⟨V, Ψ, hV, hΨ, hR⟩ :=
      GelfandCont.exists_from c T (w c) (φ c) hc.1 hcT (wle c hcI) (φle c hcI)
    set W : ℝ → ℝ := fun y => if y ≤ c then w y else V y with hW
    set Φ : ℝ → ℝ := fun y => if y ≤ c then φ y else Ψ y with hΦ
    have Wl : ∀ y, y ≤ c → W y = w y := fun y h => by rw [hW]; exact if_pos h
    have Φl : ∀ y, y ≤ c → Φ y = φ y := fun y h => by rw [hΦ]; exact if_pos h
    have Wr : ∀ y, c ≤ y → W y = V y := fun y h => by
      rcases eq_or_lt_of_le h with h | h
      · subst h; rw [hW]; exact (if_pos le_rfl).trans hV.symm
      · rw [hW]; exact if_neg (not_le.2 h)
    have Φr : ∀ y, c ≤ y → Φ y = Ψ y := fun y h => by
      rcases eq_or_lt_of_le h with h | h
      · subst h; rw [hΦ]; exact (if_pos le_rfl).trans hΨ.symm
      · rw [hΦ]; exact if_neg (not_le.2 h)
    have inL : ∀ s, 0 ≤ s → s ≤ c → s ∈ Ioo (-k) k := fun s h0 h =>
      ⟨by linarith, by linarith [hc.2]⟩
    have hG := Checked.Math.Gelfand.gelfand_ball_critical T (by linarith) W Φ
      (fun s hs => glue_at hs hc.1.le hcT hV.symm
        (fun h => by
          rw [Φl s h]; exact (dw s (inL s hs.1 h)).hasDerivWithinAt)
        (fun h => by rw [Φr s h]; exact (hR s ⟨h, hs.2⟩).1))
      (by
        have e : Φ =ᶠ[𝓝[Icc 0 T] 0] φ := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hc.1)]
            with y hy using Φl y (le_of_lt hy)
        exact ((dφ 0 (inL 0 le_rfl hc.1.le)).continuousAt.continuousWithinAt).congr_of_eventuallyEq
          e (Φl 0 hc.1.le))
      (fun s hs => by
        have hs' : s ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self hs
        exact glue_at (d := fun y => -(2 / y * Φ y) - Real.exp (W y)) hs' hc.1.le hcT hΨ.symm
          (fun h => by
            simp only [Φl s h, Wl s h]
            have hsk : s ∈ Ioo 0 k := ⟨hs.1, by linarith [hc.2]⟩
            rw [← hode' s hsk]
            exact (dφ s (inL s hs'.1 h)).hasDerivWithinAt)
          (fun h => by
            simp only [Φr s h, Wr s h]; exact (hR s ⟨h, hs.2⟩).2))
      (by rw [Wl 0 hc.1.le, w0])
    obtain ⟨s₁, -, -, hmax, -, hle⟩ := hG
    have := hmax c ⟨hc.1.le, hcT⟩
    rw [Wl c le_rfl] at this
    linarith
  -- limit c → k from the left
  have hcomp : ContinuousWithinAt (fun c => c ^ 2 * Real.exp (f (c / k) - α)) (Ioo 0 k) k := by
    have hc1 : ContinuousWithinAt f (Icc 0 1) (k / k) := by rwa [div_self hkne]
    have hm : MapsTo (fun c : ℝ => c / k) (Ioo 0 k) (Icc 0 1) := fun c hc =>
      ⟨(div_pos hc.1 hk0).le, ((div_lt_one hk0).2 hc.2).le⟩
    have h2 : ContinuousWithinAt (fun c => f (c / k)) (Ioo 0 k) k :=
      ContinuousWithinAt.comp (f := fun c : ℝ => c / k) hc1
        (continuous_id.div_const k).continuousWithinAt hm
    exact (continuous_pow 2).continuousWithinAt.mul ((h2.sub continuousWithinAt_const).rexp)
  have ht := hcomp.tendsto
  rw [nhdsWithin_Ioo_eq_nhdsLT hk0] at ht
  have hlim := le_of_tendsto ht (by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hk0]
    filter_upwards [self_mem_nhdsWithin] with c hc using key c hc)
  have hval : k ^ 2 * Real.exp (f (k / k) - α) = lam := by
    rw [div_self hkne, h1, zero_sub, hk2, Real.exp_neg]
    field_simp
  linarith [hval ▸ hlim]

end GelfandPDE

namespace GelfandPDE
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- **Gelfand problem in the unit ball of ℝ³, nonexistence above the certified bound.** If `u` is
twice continuously differentiable in the open unit ball of ℝ³, continuous on the closed ball, zero on
the unit sphere, radial (a function of `‖x‖` alone on the closed ball), and solves
`Δu + λ eᵘ = 0` in the open ball (Δ is Mathlib's Laplacian), then `λ ≤ 3.321992119`. -/
theorem gelfand_pde_radial_bound (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hrad : ∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0) :
    lam ≤ 3.321992119 := by
  rcases le_or_gt lam 0 with hl | hlam
  · linarith
  obtain ⟨g, hg⟩ := hrad
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he
  have hne : ‖e‖ = 1 := by simp [he]
  have hnorm : ∀ r : ℝ, ‖r • e‖ = |r| := fun r => by
    rw [norm_smul, hne, mul_one, Real.norm_eq_abs]
  set f : ℝ → ℝ := fun r => u (r • e) with hfdef
  have hmaps : MapsTo (fun r : ℝ => r • e) (Ioo (-1) 1) (ball 0 1) := fun r hr => by
    rw [mem_ball_zero_iff, hnorm, abs_lt]; exact hr
  have hf2 : ContDiffOn ℝ 2 f (Ioo (-1) 1) :=
    hu.comp (contDiff_id.smul contDiff_const).contDiffOn hmaps
  have hf1 : ContDiffOn ℝ 1 (deriv f) (Ioo (-1) 1) :=
    hf2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hf : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (deriv f r) r := fun r hr =>
    ((hf2.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  have hf' : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt (deriv f) (deriv (deriv f) r) r := fun r hr =>
    ((hf1.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hr)).hasDerivAt
  -- f r = g |r| near the axis
  have hfg : ∀ r ∈ Icc (-1 : ℝ) 1, f r = g |r| := fun r hr => by
    have : r • e ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_closedBall_zero_iff, hnorm, abs_le]; exact hr
    simp only [hfdef]; rw [hg _ this, hnorm]
  -- u is radial through f on the open ball
  have hradf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, u y = f ‖y‖ := fun y hy => by
    have hy' : ‖y‖ ∈ Icc (-1 : ℝ) 1 := by
      rw [mem_ball_zero_iff] at hy; exact ⟨by linarith [norm_nonneg y], hy.le⟩
    rw [hfg _ hy', abs_of_nonneg (norm_nonneg y)]
    exact hg y (ball_subset_closedBall hy)
  -- f'(0) = 0 by evenness
  have hf'0 : deriv f 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
    have hA := hf 0 h0
    have hB : HasDerivAt (fun r => f (-r)) (-deriv f 0) 0 := by
      have hn : HasDerivAt f (deriv f 0) (-(0 : ℝ)) := by rw [neg_zero]; exact hf 0 h0
      have h := hn.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      convert h using 1
      · rfl
      · ring
    have hev : (fun r => f (-r)) =ᶠ[𝓝 0] f := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
        with r hr
      rw [hfg r ⟨hr.1.le, hr.2.le⟩, hfg (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩, abs_neg]
    have := hA.unique (hB.congr_of_eventuallyEq hev.symm)
    linarith
  -- the radial ODE on (0, 1)
  have hode : ∀ r ∈ Ioo (0 : ℝ) 1,
      deriv (deriv f) r + 2 / r * deriv f r + lam * Real.exp (f r) = 0 := by
    intro r hr
    have hr' : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
    set x : EuclideanSpace ℝ (Fin 3) := r • e with hx
    have hxn : ‖x‖ = r := by rw [hx, hnorm, abs_of_pos hr.1]
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hxn; linarith [hr.1]
    have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := hmaps hr'
    have hev : u =ᶠ[𝓝 x] fun y => f ‖y‖ := by
      filter_upwards [isOpen_ball.mem_nhds hxb] with y hy using hradf y hy
    have hL := RadialLaplacian.laplacian_radial (f := f) (f' := deriv f)
      (f'' := deriv (deriv f) ‖x‖) hx0
      (by
        rw [hxn]
        filter_upwards [isOpen_Ioo.mem_nhds hr'] with ρ hρ using hf ρ hρ)
      (by rw [hxn]; exact hf' r hr')
    have h := hpde x hxb
    rw [(laplacian_congr_nhds hev).eq_of_nhds, hL, hxn, finrank_euclideanSpace_fin] at h
    have hux : u x = f r := rfl
    rw [hux] at h
    have : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
    rw [this] at h
    exact h
  have hcont : ContinuousWithinAt f (Icc 0 1) 1 := by
    have hm : MapsTo (fun r : ℝ => r • e) (Icc 0 1) (closedBall 0 1) := fun r hr => by
      rw [mem_closedBall_zero_iff, hnorm, abs_le]; exact ⟨by linarith [hr.1], hr.2⟩
    exact (hc.comp (continuous_id.smul continuous_const).continuousOn hm) 1
      ⟨zero_le_one, le_rfl⟩
  have h1 : f 1 = 0 := by
    simp only [hfdef, one_smul]; exact hb e hne
  exact ode_bound lam hlam f (deriv f) (deriv (deriv f)) hf hf' hf'0 hode hcont h1

end GelfandPDE

#print axioms GelfandPDE.gelfand_pde_radial_bound
