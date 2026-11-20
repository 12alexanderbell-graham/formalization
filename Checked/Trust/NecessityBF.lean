import Checked.Trust.NonVacuity
import Checked.Math.GelfandPDE

/-! Hypothesis necessity for `Checked.Math.GelfandPDE.gelfand_pde_radial_bound` (run 2026-11-20T1828Z):
the hypothesis that the function is twice continuously differentiable on the open ball is redundant.
With a positive parameter the equation makes the Laplacian nonzero at every point of the open ball, so the
derivative of the function is itself differentiable there (Mathlib's Laplacian of a function whose derivative
is not differentiable at a point is zero at that point). Along an axis, a radius at which the profile is not
differentiable has a whole sphere of points where the derivative is zero, so the second derivatives along the
sphere vanish and the radial one equals the Laplacian, which is nonzero; such radii are then isolated, and at an
isolated one the profile is differentiable after all (its derivative has a limit there). So the profile is
differentiable on the open interval with a differentiable derivative, satisfies the radial equation, and
`Checked.Math.GelfandODEBound.ode_bound` gives the bound. Module `NecessityBF`. -/

namespace Checked.Trust.NecessityBF
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- A derivative on a punctured neighbourhood with continuous limits extends to the point. -/
theorem nbf_hasDerivAt_punct {f g : ℝ → ℝ} {x : ℝ}
    (hd : ∀ᶠ y in 𝓝[≠] x, HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : HasDerivAt f (g x) x := by
  set s : Set ℝ := {y | HasDerivAt f (g y) y} with hs
  have hdiff : DifferentiableOn ℝ f s := fun y hy => hy.differentiableAt.differentiableWithinAt
  have hR : s ∈ 𝓝[>] x := nhdsWithin_mono x (fun y (hy : x < y) => ne_of_gt hy) hd
  have hL : s ∈ 𝓝[<] x := nhdsWithin_mono x (fun y (hy : y < x) => ne_of_lt hy) hd
  have A : HasDerivWithinAt f (g x) (Ici x) x := by
    apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hf.continuousWithinAt hR
    exact (tendsto_inf_left hg).congr' (by filter_upwards [hR] with y hy using hy.deriv.symm)
  have B : HasDerivWithinAt f (g x) (Iic x) x := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hf.continuousWithinAt hL
    exact (tendsto_inf_left hg).congr' (by filter_upwards [hL] with y hy using hy.deriv.symm)
  simpa using B.union A

/-- The Laplacian in the standard basis of three-dimensional space. -/
theorem nbf_lap_eq (u : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    Δ u x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]

/-- A nonzero Laplacian at a point needs a differentiable derivative there. -/
theorem nbf_diff_of_lap {u : EuclideanSpace ℝ (Fin 3) → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (h : Δ u x ≠ 0) : DifferentiableAt ℝ (fderiv ℝ u) x := by
  by_contra hnd
  apply h
  rw [nbf_lap_eq, fderiv_zero_of_not_differentiableAt hnd]
  simp

/-- The hypothesis `ContDiffOn ℝ 2 u (ball 0 1)` of `gelfand_pde_radial_bound` is redundant. -/
theorem gelfand_pde_radial_bound_r1 :
    dropped% Checked.Math.GelfandPDE.gelfand_pde_radial_bound 1 := by
  intro lam u hc hb hrad hpde
  rcases le_or_gt lam 0 with hl | hlam
  · linarith
  obtain ⟨g, hg⟩ := hrad
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he
  have hne : ‖e‖ = 1 := by simp [he]
  have hnorm : ∀ r : ℝ, ‖r • e‖ = |r| := fun r => by
    rw [norm_smul, hne, mul_one, Real.norm_eq_abs]
  set f : ℝ → ℝ := fun r => u (r • e) with hfdef
  set H := fderiv ℝ u with hHdef
  have hmaps : MapsTo (fun r : ℝ => r • e) (Ioo (-1) 1) (ball 0 1) := fun r hr => by
    rw [mem_ball_zero_iff, hnorm, abs_lt]; exact hr
  -- the derivative is differentiable on the open ball
  have hH : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, DifferentiableAt ℝ H x := by
    intro x hx
    apply nbf_diff_of_lap
    have h := hpde x hx
    have : lam * Real.exp (u x) ≠ 0 := (mul_pos hlam (Real.exp_pos _)).ne'
    intro h0; rw [h0] at h; exact this (by linarith)
  -- the axial derivative ψ and its derivative ψ2
  set ψ : ℝ → ℝ := fun r => H (r • e) e with hψdef
  set ψ2 : ℝ → ℝ := fun r => fderiv ℝ H (r • e) e e with hψ2def
  have hψ : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt ψ (ψ2 r) r := by
    intro r hr
    have h1 : HasDerivAt (fun s : ℝ => s • e) ((1 : ℝ) • e) r := (hasDerivAt_id r).smul_const e
    have h2 := (hH _ (hmaps hr)).hasFDerivAt.comp_hasDerivAt r h1
    have h3 := h2.clm_apply (hasDerivAt_const r e)
    simpa [Function.comp_def, hψdef, hψ2def] using h3
  have hfg : ∀ r ∈ Icc (-1 : ℝ) 1, f r = g |r| := fun r hr => by
    have : r • e ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_closedBall_zero_iff, hnorm, abs_le]; exact hr
    simp only [hfdef]; rw [hg _ this, hnorm]
  have hradf : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, u y = f ‖y‖ := fun y hy => by
    have hy' : ‖y‖ ∈ Icc (-1 : ℝ) 1 := by
      rw [mem_ball_zero_iff] at hy; exact ⟨by linarith [norm_nonneg y], hy.le⟩
    rw [hfg _ hy', abs_of_nonneg (norm_nonneg y)]
    exact hg y (ball_subset_closedBall hy)
  -- f continuous on the open interval
  have hfc : ∀ r ∈ Ioo (-1 : ℝ) 1, ContinuousAt f r := fun r hr => by
    have hb' : r • e ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := hmaps hr
    have hcu : ContinuousAt u (r • e) :=
      (hc.mono ball_subset_closedBall).continuousAt (isOpen_ball.mem_nhds hb')
    have hl : ContinuousAt (fun s : ℝ => s • e) r := (continuous_id.smul continuous_const).continuousAt
    exact ContinuousAt.comp (f := fun s : ℝ => s • e) (g := u) hcu hl
  -- radial transfer: differentiability of the profile gives that of u
  have hup : ∀ y : EuclideanSpace ℝ (Fin 3), 0 < ‖y‖ → ‖y‖ < 1 →
      DifferentiableAt ℝ f ‖y‖ → DifferentiableAt ℝ u y := by
    intro y hy0 hy1 hfd
    have hyb : y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by rw [mem_ball_zero_iff]; exact hy1
    have hev : u =ᶠ[𝓝 y] fun z => f ‖z‖ := by
      filter_upwards [isOpen_ball.mem_nhds hyb] with z hz using hradf z hz
    have hn := (Checked.Math.RadialLaplacian.hasFDerivAt_norm (norm_pos_iff.1 hy0)).differentiableAt
    exact (hfd.comp y hn).congr_of_eventuallyEq hev
  -- and conversely
  have hdown : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ = r →
      DifferentiableAt ℝ u y → DifferentiableAt ℝ f r := by
    intro r hr y hy hud
    have hr0 : r ≠ 0 := hr.1.ne'
    have hud' : DifferentiableAt ℝ u ((r / r) • y) := by rwa [div_self hr0, one_smul]
    have hd : DifferentiableAt ℝ (fun s : ℝ => u ((s / r) • y)) r :=
      hud'.comp r ((differentiableAt_id.div_const r).smul_const y)
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds (show r ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hr.1], hr.2⟩)]
      with s hs
    have hsn : ‖(s / r) • y‖ = |s| := by
      rw [norm_smul, hy, Real.norm_eq_abs, abs_div, abs_of_pos hr.1, div_mul_cancel₀ _ hr0]
    have hmem : (s / r) • y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_closedBall_zero_iff, hsn, abs_le]; exact ⟨hs.1.le, hs.2.le⟩
    rw [hfg s ⟨hs.1.le, hs.2.le⟩, hg _ hmem, hsn]
  -- a non-differentiable radius: the derivative vanishes on its whole sphere
  have hsph : ∀ r ∈ Ioo (0 : ℝ) 1, ¬ DifferentiableAt ℝ f r →
      ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ = r → H y = 0 := by
    intro r hr hnd y hy
    exact fderiv_zero_of_not_differentiableAt (fun hud => hnd (hdown r hr y hy hud))
  -- the tangential second derivatives vanish there
  have htan : ∀ r ∈ Ioo (0 : ℝ) 1, ¬ DifferentiableAt ℝ f r → ∀ j : Fin 3, j ≠ 0 →
      fderiv ℝ H (r • e) (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) = 0 := by
    intro r hr hnd j hj
    set ej : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single j 1 with hej
    have hinner : inner ℝ e ej = 0 := by
      simp [he, hej, EuclideanSpace.inner_single_left, Ne.symm hj]
    have hej1 : ‖ej‖ = 1 := by simp [hej]
    set c : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => (r * Real.cos t) • e + (r * Real.sin t) • ej
      with hcdef
    have hcn : ∀ t, ‖c t‖ = r := by
      intro t
      have h2 : ‖c t‖ ^ 2 = r ^ 2 := by
        simp only [hcdef]
        rw [norm_add_sq_real, inner_smul_left, inner_smul_right, hinner, norm_smul, norm_smul,
          hne, hej1, Real.norm_eq_abs, Real.norm_eq_abs]
        simp only [mul_one, mul_zero, RCLike.conj_to_real]
        have := Real.cos_sq_add_sin_sq t
        rw [sq_abs, sq_abs, mul_pow, mul_pow]
        nlinarith [this]
      exact (sq_eq_sq₀ (norm_nonneg _) hr.1.le).1 h2
    have hc0 : c 0 = r • e := by simp [hcdef]
    have hcd : HasDerivAt c ((r * -Real.sin 0) • e + (r * Real.cos 0) • ej) 0 :=
      (((Real.hasDerivAt_cos 0).const_mul r).smul_const e).add
        (((Real.hasDerivAt_sin 0).const_mul r).smul_const ej)
    have hcd' : HasDerivAt c (r • ej) 0 := by simpa using hcd
    have hrb : r • e ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_ball_zero_iff, hnorm, abs_of_pos hr.1]; exact hr.2
    have hHd : HasFDerivAt H (fderiv ℝ H (c 0)) (c 0) := by rw [hc0]; exact (hH _ hrb).hasFDerivAt
    have hcomp := hHd.comp_hasDerivAt (0 : ℝ) hcd'
    have hzero : (H ∘ c) = fun _ => (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := by
      funext t; exact hsph r hr hnd (c t) (hcn t)
    rw [hzero] at hcomp
    have huniq := hcomp.unique (hasDerivAt_const (0 : ℝ) (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ))
    rw [hc0, ContinuousLinearMap.map_smul] at huniq
    have : fderiv ℝ H (r • e) ej = 0 := (smul_eq_zero.1 huniq).resolve_left hr.1.ne'
    rw [this]; rfl
  -- so the radial second derivative is the Laplacian, which is nonzero
  have hrad2 : ∀ r ∈ Ioo (0 : ℝ) 1, ¬ DifferentiableAt ℝ f r → ψ2 r ≠ 0 := by
    intro r hr hnd h0
    have hrb : r • e ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      rw [mem_ball_zero_iff, hnorm, abs_of_pos hr.1]; exact hr.2
    have h := hpde _ hrb
    rw [nbf_lap_eq, Fin.sum_univ_three, htan r hr hnd 1 (by decide),
      htan r hr hnd 2 (by decide)] at h
    have h0' : fderiv ℝ H (r • e) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = 0 := h0
    rw [← hHdef] at h
    rw [h0'] at h
    have : lam * Real.exp (u (r • e)) > 0 := mul_pos hlam (Real.exp_pos _)
    linarith
  -- the profile is differentiable on (0, 1)
  have hdf : ∀ r ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ f r := by
    intro r hr
    by_contra hnd
    have hr' : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
    by_cases hfr : ∃ᶠ s in 𝓝[≠] r, ¬ DifferentiableAt ℝ f s
    · -- accumulation of bad radii: the radial second derivative vanishes
      apply hrad2 r hr hnd
      have hsl := (hψ r hr').tendsto_slope
      have hψr : ψ r = 0 := by
        simp only [hψdef]
        rw [hsph r hr hnd (r • e) (by rw [hnorm, abs_of_pos hr.1])]; rfl
      have hin : ∀ᶠ s in 𝓝[≠] r, s ∈ Ioo (0 : ℝ) 1 :=
        nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hr)
      have hfreq : ∃ᶠ s in 𝓝[≠] r, slope ψ r s = (fun _ => (0 : ℝ)) s := by
        apply (hfr.and_eventually hin).mono
        intro s ⟨hs1, hs2⟩
        have : ψ s = 0 := by
          simp only [hψdef]
          rw [hsph s hs2 hs1 (s • e) (by rw [hnorm, abs_of_pos hs2.1])]; rfl
        simp [slope_def_field, this, hψr]
      exact tendsto_nhds_unique_of_frequently_eq hsl tendsto_const_nhds hfreq
    · -- isolated: the profile is differentiable there after all
      rw [not_frequently] at hfr
      have hin : ∀ᶠ s in 𝓝[≠] r, s ∈ Ioo (0 : ℝ) 1 :=
        nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hr)
      have hd : ∀ᶠ s in 𝓝[≠] r, HasDerivAt f (ψ s) s := by
        filter_upwards [hfr, hin] with s hs1 hs2
        have hsn : ‖s • e‖ = s := by rw [hnorm, abs_of_pos hs2.1]
        have hud : DifferentiableAt ℝ u (s • e) :=
          hup (s • e) (by rw [hsn]; exact hs2.1) (by rw [hsn]; exact hs2.2) (by rw [hsn]; exact not_not.1 hs1)
        have h1 : HasDerivAt (fun t : ℝ => t • e) ((1 : ℝ) • e) s := (hasDerivAt_id s).smul_const e
        have h2 := hud.hasFDerivAt.comp_hasDerivAt s h1
        simpa [Function.comp_def, hψdef, hHdef, hfdef] using h2
      exact hnd (nbf_hasDerivAt_punct hd (hfc r hr') (hψ r hr').continuousAt).differentiableAt
  -- the derivative of the profile on (-1, 1)
  have hfne : ∀ r ∈ Ioo (-1 : ℝ) 1, r ≠ 0 → HasDerivAt f (ψ r) r := by
    intro r hr hr0
    have hsn : ‖r • e‖ = |r| := hnorm r
    have hpos : 0 < |r| := abs_pos.2 hr0
    have hlt : |r| < 1 := abs_lt.2 hr
    have hud : DifferentiableAt ℝ u (r • e) :=
      hup (r • e) (by rw [hsn]; exact hpos) (by rw [hsn]; exact hlt)
        (by rw [hsn]; exact hdf |r| ⟨hpos, hlt⟩)
    have h1 : HasDerivAt (fun t : ℝ => t • e) ((1 : ℝ) • e) r := (hasDerivAt_id r).smul_const e
    have h2 := hud.hasFDerivAt.comp_hasDerivAt r h1
    simpa [Function.comp_def, hψdef, hHdef, hfdef] using h2
  have hf : ∀ r ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (ψ r) r := by
    intro r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
      apply nbf_hasDerivAt_punct _ (hfc 0 h0) (hψ 0 h0).continuousAt
      have hin : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ∈ Ioo (-1 : ℝ) 1 :=
        nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds h0)
      filter_upwards [hin, self_mem_nhdsWithin] with s hs hs0
      exact hfne s hs hs0
    · exact hfne r hr hr0
  -- ψ(0) = 0 by evenness
  have hψ0 : ψ 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
    have hA := hf 0 h0
    have hB : HasDerivAt (fun r => f (-r)) (-ψ 0) 0 := by
      have hn : HasDerivAt f (ψ 0) (-(0 : ℝ)) := by rw [neg_zero]; exact hf 0 h0
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
  have hode : ∀ r ∈ Ioo (0 : ℝ) 1, ψ2 r + 2 / r * ψ r + lam * Real.exp (f r) = 0 := by
    intro r hr
    have hr' : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
    set x : EuclideanSpace ℝ (Fin 3) := r • e with hx
    have hxn : ‖x‖ = r := by rw [hx, hnorm, abs_of_pos hr.1]
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hxn; linarith [hr.1]
    have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := hmaps hr'
    have hev : u =ᶠ[𝓝 x] fun y => f ‖y‖ := by
      filter_upwards [isOpen_ball.mem_nhds hxb] with y hy using hradf y hy
    have hL := Checked.Math.RadialLaplacian.laplacian_radial (f := f) (f' := ψ)
      (f'' := ψ2 ‖x‖) hx0
      (by
        rw [hxn]
        filter_upwards [isOpen_Ioo.mem_nhds hr'] with ρ hρ using hf ρ hρ)
      (by rw [hxn]; exact hψ r hr')
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
  exact Checked.Math.GelfandODEBound.ode_bound lam hlam f ψ ψ2 hf hψ hψ0 hode hcont h1

end Checked.Trust.NecessityBF
