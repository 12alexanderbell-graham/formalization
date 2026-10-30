import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lookback time to second order in redshift (target 1, milestone 1; PROMOTED)

Conventions (annex XLI):
* Cosmic time `t : ℝ`, observation time `t₀`. Scale factor `a : ℝ → ℝ`. Units: any; `c` does
  not appear (lookback time is a time).
* `H₀ = a'(t₀) / a(t₀)` (Physlib `Cosmology.FLRW.hubbleConstant`).
* `q₀ = -(a''(t₀) a(t₀)) / a'(t₀)²` (Physlib `Cosmology.FLRW.decelerationParameter`).
* Redshift of a source emitting at `t`: `z(t) = a(t₀) / a(t) - 1` (Physlib `FLRW.redshift`).
* `deriv` of a non-differentiable function is junk (`0`); every derivative used is assumed to
  exist.

Model assumptions as hypotheses: `a` is differentiable near `t₀`, `a'` is differentiable at
`t₀` (Physlib's `FLRW` structure assumes the same on its open interval), `a(t₀) ≠ 0`,
`a'(t₀) ≠ 0` (i.e. `H₀ ≠ 0`). No field equations are used: the statement is kinematic.

Source: Physlib `Physlib/Cosmology/FLRW/Distances.lean` TODO ("prove its model-independent
expansion `t₀ - t = H₀⁻¹ [z - ½(2 + q₀) z² + …]`"); M. Visser, "Cosmography: Cosmology
without the Einstein equations", Gen. Rel. Grav. 37 (2005) 1541, arXiv:gr-qc/0411131,
Eq. (11) with `D = c Δt` (Eq. (7)).

Reading of "+ …" (Underspecified, recorded in the audit): with only two derivatives of `a`
the remainder is `o(z²)` (Peano form). The `O(z³)` form under three derivatives is a separate
statement.
-/

namespace Checked.Cosmography

open Filter Asymptotics Topology

/-- Peano second-order Taylor: twice differentiable at `t₀` (differentiable near). -/
theorem peano2 (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀) :
    (fun t => a t - (a t₀ + deriv a t₀ * (t - t₀) + deriv (deriv a) t₀ / 2 * (t - t₀) ^ 2))
      =o[𝓝 t₀] (fun t => (t - t₀) ^ 2) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 ha
  set A1 := deriv a t₀
  set A2 := deriv (deriv a) t₀
  let f : ℝ → ℝ := fun t => a t - A1 * (t - t₀) - A2 / 2 * (t - t₀) ^ 2
  let f' : ℝ → ℝ := fun t => deriv a t - A1 - A2 * (t - t₀)
  have hs : IsOpen (Metric.ball t₀ δ) := Metric.isOpen_ball
  have hmem : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
  have hff' : ∀ x ∈ Metric.ball t₀ δ, HasDerivWithinAt f (f' x) (Metric.ball t₀ δ) x := by
    intro x hx
    have h1 := (hball x hx).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => A1 * (t - t₀)) (A1 * 1) x :=
      ((hasDerivAt_id x).sub_const t₀).const_mul A1
    have h3 : HasDerivAt (fun t : ℝ => A2 / 2 * (t - t₀) ^ 2)
        (A2 / 2 * ((2:ℕ) * (x - t₀) ^ 1 * 1)) x :=
      (((hasDerivAt_id x).sub_const t₀).pow 2).const_mul (A2 / 2)
    have := (h1.sub h2).sub h3
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [f']; push_cast; ring
  have hf' : f' =o[𝓝[Metric.ball t₀ δ] t₀] fun x => (x - t₀) ^ 1 := by
    rw [hs.nhdsWithin_eq hmem]
    have := ha'.hasDerivAt.isLittleO
    refine this.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [f', smul_eq_mul]; ring
    · simp
  have key := (convex_ball t₀ δ).isLittleO_pow_succ_real hmem hff' hf'
  rw [hs.nhdsWithin_eq hmem] at key
  refine key.congr' (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · simp only [f]; ring
  · ring

theorem powo (t₀ : ℝ) {n m : ℕ} (h : n < m) :
    (fun x : ℝ => (x - t₀) ^ m) =o[𝓝 t₀] fun x => (x - t₀) ^ n :=
  (isLittleO_pow_pow h).comp_tendsto (tendsto_sub_nhds_zero_iff.2 tendsto_id)


/-- Hubble parameter at `t`: `a'(t) / a(t)`. Mirrors Physlib `hubbleConstant`. -/
noncomputable def hubble (a : ℝ → ℝ) (t : ℝ) : ℝ := deriv a t / a t

/-- Deceleration parameter at `t`: `-(a''(t) a(t)) / a'(t)²`. Mirrors Physlib
`decelerationParameter`. -/
noncomputable def decel (a : ℝ → ℝ) (t : ℝ) : ℝ := -(deriv (deriv a) t * a t) / deriv a t ^ 2

/-- Redshift at observation time `t₀` of a source emitting at `t`: `a(t₀)/a(t) - 1`.
Mirrors Physlib `FLRW.redshift`. -/
noncomputable def redshift (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := a t₀ / a t - 1

/-- **Milestone 1** (frozen in commit 6ef1003, audited in runs/2026-10-30T0028Z/audit.md). The lookback time `t₀ - t` of a source with redshift
`z = z(t)` satisfies `t₀ - t = H₀⁻¹ (z - (1 + q₀/2) z²) + o(z²)` as `t → t₀`. -/
theorem lookback_second_order (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ a t)
    (ha' : DifferentiableAt ℝ (deriv a) t₀)
    (ha0 : a t₀ ≠ 0) (hH : deriv a t₀ ≠ 0) :
    (fun t => (t₀ - t) - (redshift a t₀ t - (1 + decel a t₀ / 2) * redshift a t₀ t ^ 2)
        / hubble a t₀)
      =o[𝓝 t₀] (fun t => redshift a t₀ t ^ 2) := by
  set A0 := a t₀ with hA0
  set A1 := deriv a t₀ with hA1
  set A2 := deriv (deriv a) t₀ with hA2
  set H := hubble a t₀ with hHdef
  set k := 1 + decel a t₀ / 2 with hk
  have hH0 : H ≠ 0 := div_ne_zero hH ha0
  set c2 := A1 ^ 2 / A0 ^ 2 - A2 / (2 * A0) with hc2
  have hc2k : c2 = k * H ^ 2 := by
    simp only [hc2, hk, hHdef, hubble, decel, ← hA0, ← hA1, ← hA2]; field_simp; ring
  -- Taylor remainder of `a`
  set e : ℝ → ℝ := fun t => a t - (A0 + A1 * (t - t₀) + A2 / 2 * (t - t₀) ^ 2) with he
  have he_o : e =o[𝓝 t₀] (fun t => (t - t₀) ^ 2) := peano2 a t₀ ha ha'
  set z : ℝ → ℝ := fun t => redshift a t₀ t with hz
  set P : ℝ → ℝ := fun t => -H * (t - t₀) + c2 * (t - t₀) ^ 2 with hP
  set R : ℝ → ℝ := fun t => (c2 * A1 - H * A2 / 2) * (t - t₀) ^ 3 + c2 * A2 / 2 * (t - t₀) ^ 4
    with hR
  have hcont : ContinuousAt a t₀ := ha.self_of_nhds.continuousAt
  have hane : ∀ᶠ t in 𝓝 t₀, a t ≠ 0 := hcont.eventually_ne ha0
  -- step 2: expansion of the redshift
  have hzeq : ∀ᶠ t in 𝓝 t₀, z t - P t = (a t)⁻¹ * (-(e t) * (1 + P t) - R t) := by
    filter_upwards [hane] with t ht
    simp only [hz, hP, hR, he, redshift, hHdef, hubble, ← hA0, ← hA1, hc2]
    field_simp
    ring
  have hR_o : R =o[𝓝 t₀] (fun t => (t - t₀) ^ 2) :=
    ((powo t₀ (by norm_num : 2 < 3)).const_mul_left _).add
      ((powo t₀ (by norm_num : 2 < 4)).const_mul_left _)
  have hPt : Tendsto P (𝓝 t₀) (𝓝 0) := by
    have : Continuous P := by fun_prop
    simpa [hP] using this.tendsto t₀
  have hinv : (fun t => (a t)⁻¹) =O[𝓝 t₀] (fun _ => (1:ℝ)) :=
    (hcont.inv₀ ha0).isBigO_one ℝ
  have h1P : (fun t => 1 + P t) =O[𝓝 t₀] (fun _ => (1:ℝ)) :=
    ((tendsto_const_nhds.add hPt)).isBigO_one ℝ
  have hr_o : (fun t => z t - P t) =o[𝓝 t₀] (fun t => (t - t₀) ^ 2) := by
    refine IsLittleO.congr' ?_ (hzeq.mono fun t ht => ht.symm) EventuallyEq.rfl
    have : (fun t => -(e t) * (1 + P t) - R t) =o[𝓝 t₀] (fun t => (t - t₀) ^ 2) := by
      refine IsLittleO.sub ?_ hR_o
      have := he_o.neg_left.mul_isBigO h1P
      simpa using this
    simpa using hinv.mul_isLittleO this
  -- step 3: the lookback combination
  set r : ℝ → ℝ := fun t => z t - P t with hr
  set S : ℝ → ℝ := fun t => -2 * H * c2 * (t - t₀) ^ 3 + c2 ^ 2 * (t - t₀) ^ 4
      + r t * (2 * P t + r t) with hS
  have hLeq : ∀ t, (t₀ - t) - (z t - k * z t ^ 2) / H = (-1 / H) * r t + k / H * S t := by
    intro t
    have hzt : z t = P t + r t := by simp [hr]
    rw [hzt]
    simp only [hP, hS, hc2k]
    field_simp
    ring
  have hS_o : S =o[𝓝 t₀] (fun t => (t - t₀) ^ 2) := by
    refine ((((powo t₀ (by norm_num : 2 < 3)).const_mul_left _).add
      ((powo t₀ (by norm_num : 2 < 4)).const_mul_left _))).add ?_
    have h2 : (fun t => 2 * P t + r t) =O[𝓝 t₀] (fun _ => (1:ℝ)) := by
      have hrt : Tendsto r (𝓝 t₀) (𝓝 0) :=
        hr_o.trans_tendsto (by
          have hc : Continuous fun t : ℝ => (t - t₀) ^ 2 := by fun_prop
          have := hc.tendsto t₀
          simpa using this)
      exact ((hPt.const_mul 2).add hrt).isBigO_one ℝ
    simpa using hr_o.mul_isBigO h2
  have hL_o : (fun t => (t₀ - t) - (z t - k * z t ^ 2) / H) =o[𝓝 t₀] (fun t => (t - t₀) ^ 2) := by
    simp_rw [hLeq]
    exact (hr_o.const_mul_left _).add (hS_o.const_mul_left _)
  -- step 4: (t - t₀)² = O(z²)
  have hzO : (fun t => t - t₀) =O[𝓝 t₀] z := by
    have hsmall : (fun t => c2 * (t - t₀) ^ 2 + r t) =o[𝓝 t₀] (fun t => -H * (t - t₀)) := by
      have h2 : (fun t => (t - t₀) ^ 2) =o[𝓝 t₀] (fun t => -H * (t - t₀)) := by
        have := (powo t₀ (by norm_num : 1 < 2)).trans_isBigO
          (isBigO_self_const_mul (neg_ne_zero.2 hH0) (fun t => (t - t₀) ^ 1) (𝓝 t₀))
        simpa using this
      exact (h2.const_mul_left c2).add (hr_o.trans h2)
    have := hsmall.right_isBigO_add
    have hzz : (fun t => c2 * (t - t₀) ^ 2 + r t + -H * (t - t₀)) = z := by
      funext t; simp only [hr, hP]; ring
    rw [hzz] at this
    exact (isBigO_self_const_mul (neg_ne_zero.2 hH0) (fun t => t - t₀) (𝓝 t₀)).trans this
  exact hL_o.trans_isBigO (hzO.pow 2)

end Checked.Cosmography
