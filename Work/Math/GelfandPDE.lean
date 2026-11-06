import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.PicardLindelof
import Work.Math.RadialLaplacian
import Work.Math.GelfandODEBound

/-!
# Mathematics (THE RESULT part 5): the Gelfand problem in the unit ball of ℝ³ as a PDE —
# nonexistence of radial solutions above the certified bound

**Question.** The Gelfand (Frank-Kamenetskii) problem is Δu + λ eᵘ = 0 in the unit ball B of ℝ³,
u = 0 on the sphere ∂B. `Checked.Math.Gelfand.gelfand_ball_critical` certifies a statement about the
radial ODE w'' + (2/s) w' + eʷ = 0, w(0) = 0: the maximum of s² e^{w(s)}. What links that ODE
statement to the PDE (the radial Laplacian in ℝ³, the scaling u(r) = w(k r) − w(k), λ = k² e^{w(k)},
solutions with k < 41/10 that the ODE statement does not see) was prose until now.

**What is stated here** (frozen before the proof is committed, annex 40.1). For every real λ and
every u : ℝ³ → ℝ that is twice continuously differentiable on the open unit ball, continuous on the
closed unit ball, zero on the unit sphere, radial on the closed ball (u x = g ‖x‖ for some g), and
solves Δu x + λ e^{u x} = 0 at every x of the open ball, with Δ Mathlib's Laplacian on
`EuclideanSpace ℝ (Fin 3)`: λ ≤ 3.321992119.

**Not stated here:** existence of a radial solution for every 0 < λ ≤ 3.321992118 (the other half of
"λ* is the supremum of solvable λ"); that every classical solution is radial (Gidas–Ni–Nirenberg);
non-radial or weak solutions.

Only Mathlib definitions occur in the statement (no program definition to pin).
-/

namespace Work.Math.GelfandPDE
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of ℝ³, radial solutions: if u is twice continuously
differentiable on the open unit ball, continuous on the closed unit ball, zero on the unit sphere,
a function of ‖x‖ alone on the closed ball, and Δu + λ eᵘ = 0 holds at every point of the open ball
(Δ is Mathlib's Laplacian), then λ ≤ 3.321992119. -/
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
    have hL := Work.Math.RadialLaplacian.laplacian_radial (f := f) (f' := deriv f)
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
  exact Work.Math.GelfandODEBound.ode_bound lam hlam f (deriv f) (deriv (deriv f)) hf hf' hf'0 hode hcont h1

end Work.Math.GelfandPDE
