import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Weak maximum principle for superharmonic functions on the unit ball of ℝ³

A `C²` function on the open unit ball of `EuclideanSpace ℝ (Fin 3)`, continuous on the closed
ball, nonnegative on the unit sphere and with `Δ v ≤ 0` (Mathlib's Laplacian) on the open ball,
is nonnegative on the closed ball.
-/

namespace Work.Math.GMaxPrinciple
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- The Laplacian on `ℝ³` as the sum of the pure second derivatives along the standard basis. -/
theorem gmp_lap_eq (u : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    Δ u x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]

/-- One-dimensional second-derivative test: at a local minimum the second derivative is `≥ 0`. -/
theorem gmp_second_nonneg (f : ℝ → ℝ) (x₀ : ℝ) (hmin : IsLocalMin f x₀)
    (hc : ContinuousAt f x₀) : 0 ≤ deriv (deriv f) x₀ := by
  by_contra hneg
  push Not at hneg
  have hd : deriv f x₀ = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax f x₀ := isLocalMax_of_deriv_deriv_neg hneg hd hc
  have hconst : f =ᶠ[𝓝 x₀] fun _ => f x₀ := by
    filter_upwards [hmin, hmax] with t h1 h2
    exact le_antisymm h2 h1
  have h2 : deriv f =ᶠ[𝓝 x₀] deriv (fun _ : ℝ => f x₀) := hconst.deriv
  have h3 : deriv (deriv f) x₀ = deriv (deriv (fun _ : ℝ => f x₀)) x₀ := h2.deriv_eq
  simp at h3
  linarith

/-- At an interior local minimum of a function that is `C²` near the point, `Δ u ≥ 0`. -/
theorem gmp_lap_nonneg_of_min (u : EuclideanSpace ℝ (Fin 3) → ℝ) (x₀ : EuclideanSpace ℝ (Fin 3))
    (hu : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 2 u y) (hmin : IsLocalMin u x₀) : 0 ≤ Δ u x₀ := by
  rw [gmp_lap_eq]
  apply Finset.sum_nonneg
  intro i _
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i 1 with he
  set g : ℝ → ℝ := fun t => u (x₀ + t • e) with hg
  have hT : Tendsto (fun t : ℝ => x₀ + t • e) (𝓝 0) (𝓝 x₀) := by
    have hcont : Continuous fun t : ℝ => x₀ + t • e := by fun_prop
    exact hcont.tendsto' 0 x₀ (by simp)
  have hgmin : IsLocalMin g 0 := by
    have h0 : g 0 = u x₀ := by simp [hg]
    unfold IsLocalMin IsMinFilter
    filter_upwards [hT.eventually hmin] with t ht
    rw [h0]; exact ht
  have hx₀ : ContDiffAt ℝ 2 u x₀ := hu.self_of_nhds
  -- first derivative of `g` near `0`
  have hgd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (fderiv ℝ u (x₀ + t • e) e) t := by
    filter_upwards [hT.eventually hu] with t ht
    have hdu : DifferentiableAt ℝ u (x₀ + t • e) := ht.differentiableAt (by norm_num)
    have h1 : HasDerivAt (fun s : ℝ => x₀ + s • e) ((1 : ℝ) • e) t :=
      ((hasDerivAt_id t).smul_const e).const_add x₀
    have h2 := hdu.hasFDerivAt.comp_hasDerivAt t h1
    simpa [Function.comp_def, hg] using h2
  have hdg : deriv g =ᶠ[𝓝 0] fun t => fderiv ℝ u (x₀ + t • e) e := by
    filter_upwards [hgd] with t ht
    exact ht.deriv
  -- second derivative of `g` at `0`
  have hH : DifferentiableAt ℝ (fderiv ℝ u) x₀ :=
    (hx₀.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hψ : HasDerivAt (fun t : ℝ => fderiv ℝ u (x₀ + t • e) e)
      (fderiv ℝ (fderiv ℝ u) x₀ e e) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => x₀ + s • e) ((1 : ℝ) • e) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x₀
    have hH' : DifferentiableAt ℝ (fderiv ℝ u) (x₀ + (0 : ℝ) • e) := by simpa using hH
    have h2 := hH'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 := h2.clm_apply (hasDerivAt_const (0 : ℝ) e)
    simpa [Function.comp_def] using h3
  have hgc : ContinuousAt g 0 := (hgd.self_of_nhds).continuousAt
  have key := gmp_second_nonneg g 0 hgmin hgc
  rw [hdg.deriv_eq, hψ.deriv] at key
  exact key

/-- The Laplacian of `‖x‖²` on `ℝ³` is `6`. -/
theorem gmp_lap_norm_sq (x : EuclideanSpace ℝ (Fin 3)) :
    Δ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2) x = 6 := by
  rw [gmp_lap_eq, fderiv_norm_sq]
  rw [← FunLike.coe_smul, ContinuousLinearMap.fderiv]
  have h : ∀ i : Fin 3, (innerSL ℝ (EuclideanSpace.single i (1 : ℝ) :
      EuclideanSpace ℝ (Fin 3))) (EuclideanSpace.single i 1) = 1 := fun i => by simp
  simp only [Fin.sum_univ_three, smul_apply]
  erw [h 0, h 1, h 2]
  norm_num

theorem superharmonic_nonneg (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hv : ContDiffOn ℝ 2 v (ball 0 1))
    (hc : ContinuousOn v (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → 0 ≤ v x)
    (hΔ : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ v x ≤ 0) :
    ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, 0 ≤ v x := by
  intro x hx
  -- for every `ε > 0`, `v x ≥ -ε`
  have hε : ∀ ε : ℝ, 0 < ε → -ε ≤ v x := by
    intro ε hεpos
    set q : EuclideanSpace ℝ (Fin 3) → ℝ := ε • fun y => ‖y‖ ^ 2 with hq
    set w : EuclideanSpace ℝ (Fin 3) → ℝ := v - q with hw
    have hqapp : ∀ y, q y = ε * ‖y‖ ^ 2 := fun y => by simp [hq]
    have hqcd : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
    have hwc : ContinuousOn w (closedBall 0 1) :=
      hc.sub ((hqcd.const_smul ε).continuous.continuousOn)
    obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).exists_isMinOn
      ⟨0, mem_closedBall_self zero_le_one⟩ hwc
    have hx₀n : ‖x₀‖ = 1 := by
      by_contra hne
      have hx₀b : x₀ ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
        rw [mem_closedBall_zero_iff] at hx₀
        rw [mem_ball_zero_iff]; exact lt_of_le_of_ne hx₀ hne
      have hloc : IsLocalMin w x₀ :=
        hmin.isLocalMin (mem_of_superset (isOpen_ball.mem_nhds hx₀b) ball_subset_closedBall)
      have hcd : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ContDiffAt ℝ 2 w y := fun y hy =>
        (hv.contDiffAt (isOpen_ball.mem_nhds hy)).sub (hqcd.const_smul ε).contDiffAt
      have hnn := gmp_lap_nonneg_of_min w x₀
        (eventually_of_mem (isOpen_ball.mem_nhds hx₀b) hcd) hloc
      have hvx : ContDiffAt ℝ 2 v x₀ := hv.contDiffAt (isOpen_ball.mem_nhds hx₀b)
      have hqx : ContDiffAt ℝ 2 q x₀ := hqcd.contDiffAt.const_smul ε
      have hlap : Δ w x₀ = Δ v x₀ - ε * 6 := by
        rw [hw, hvx.laplacian_sub hqx, hq, laplacian_smul ε hqcd.contDiffAt, gmp_lap_norm_sq]
        simp
      have := hΔ x₀ hx₀b
      linarith
    have h1 : w x₀ ≤ w x := hmin hx
    have h2 : w x₀ = v x₀ - ε := by simp [hw, hqapp, hx₀n]
    have h3 : w x = v x - ε * ‖x‖ ^ 2 := by simp [hw, hqapp]
    have h4 := hb x₀ hx₀n
    have h5 : 0 ≤ ε * ‖x‖ ^ 2 := by positivity
    linarith
  by_contra hneg
  push Not at hneg
  have := hε (-v x / 2) (by linarith)
  linarith

end Work.Math.GMaxPrinciple
