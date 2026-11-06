import Mathlib

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
