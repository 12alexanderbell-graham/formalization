import Checked.Math.BEFocus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

/-- The cosine of the angle in the Jordan basis, measured from the ray of `y = 0` on the side `σ`. -/
noncomputable def fc (σ : ℝ) (U V : ℝ → ℝ) (t : ℝ) : ℝ :=
  σ * (4 * (U t - 1) + (V t - 2)) / Real.sqrt (2 * Nw (U t - 1) (V t - 2))

/-- The angle. -/
noncomputable def th (σ : ℝ) (U V : ℝ → ℝ) (t : ℝ) : ℝ := Real.arccos (fc σ U V t)

theorem two_N_eq (x y : ℝ) : 2 * Nw x y = (4 * x + y) ^ 2 + 7 * y ^ 2 := by unfold Nw; ring

/-- The algebraic identity behind the angle's derivative. -/
theorem ang_id (x y : ℝ) :
    28 * y * Lq x y = (4 * x + y) * Dq x y - 2 * Nw x y * (4 * ((1 + x) * (-x - y)) + (2 + y) * x) := by
  unfold Lq Dq Nw; ring

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem fc_cont : ContinuousOn (fc σ U V) (Ici s0) := by
  intro t ht
  have hN := S.N_pos ht
  have hU := (S.hU t ht).continuousAt
  have hV := (S.hV t ht).continuousAt
  have hNc : ContinuousAt (fun t => Nw (U t - 1) (V t - 2)) t := (S.dN ht).continuousAt
  have hr : Real.sqrt (2 * Nw (U t - 1) (V t - 2)) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  apply ContinuousAt.continuousWithinAt
  unfold fc
  exact ((continuousAt_const.mul ((continuousAt_const.mul (hU.sub continuousAt_const)).add
    (hV.sub continuousAt_const))).div ((continuousAt_const.mul hNc).sqrt) hr)

theorem th_cont : ContinuousOn (th σ U V) (Ici s0) :=
  Real.continuous_arccos.comp_continuousOn (fc_cont S)

theorem th_deriv {σ t : ℝ} (hσ : σ ^ 2 = 1) (ht : t ∈ Ici s0) (hy : 0 < σ * (V t - 2)) :
    HasDerivAt (th σ U V)
      (2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t)) t := by
  set x := U t - 1 with hx
  set y := V t - 2 with hy'
  set N := Nw x y with hNdef
  have tp := S.tpos ht
  have hN : 0 < N := S.N_pos ht
  set r := Real.sqrt (2 * N) with hr
  have r0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have rr : r ^ 2 = 2 * N := Real.sq_sqrt (by linarith)
  have s7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have s7p : 0 < Real.sqrt 7 := by positivity
  have hp : HasDerivAt (fun t => 4 * (U t - 1) + (V t - 2))
      (4 * (U t * (3 - U t - V t) / t) + V t * (U t - 1) / t) t :=
    (((S.hU t ht).sub_const 1).const_mul 4).add ((S.hV t ht).sub_const 2)
  have hrd : HasDerivAt (fun t => Real.sqrt (2 * Nw (U t - 1) (V t - 2)))
      (2 * (Dq x y / t) / (2 * r)) t :=
    ((S.dN ht).const_mul 2).sqrt (by rw [← hNdef]; linarith)
  have hf : HasDerivAt (fc σ U V)
      ((σ * (4 * (U t * (3 - U t - V t) / t) + V t * (U t - 1) / t) * r
        - σ * (4 * x + y) * (2 * (Dq x y / t) / (2 * r))) / r ^ 2) t := by
    have := (hp.const_mul σ).div hrd r0.ne'
    unfold fc
    convert this using 1
  have h1f : 1 - fc σ U V t ^ 2 = (Real.sqrt 7 * (σ * y) / r) ^ 2 := by
    unfold fc
    rw [← hr]
    rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, rr, s7, hσ]
    have := two_N_eq x y
    field_simp
    linarith
  have hsq : Real.sqrt (1 - fc σ U V t ^ 2) = Real.sqrt 7 * (σ * y) / r := by
    rw [h1f]; exact Real.sqrt_sq (by positivity)
  have hne1 : fc σ U V t ≠ 1 := by
    intro h; have := h1f; rw [h] at this
    have : 0 < (Real.sqrt 7 * (σ * y) / r) ^ 2 := by positivity
    linarith
  have hne2 : fc σ U V t ≠ -1 := by
    intro h; have := h1f; rw [h] at this
    have : 0 < (Real.sqrt 7 * (σ * y) / r) ^ 2 := by positivity
    linarith
  have ha := (Real.hasDerivAt_arccos hne2 hne1).comp t hf
  unfold th
  refine ha.congr_deriv ?_
  rw [hsq]
  have hU1 : U t = 1 + x := by rw [hx]; ring
  have hV2 : V t = 2 + y := by rw [hy']; ring
  rw [hU1, hV2]
  have hid := ang_id x y
  have hyne : y ≠ 0 := by rintro h; rw [h] at hy; simp at hy
  have hσne : σ ≠ 0 := by rintro h; rw [h] at hσ; norm_num at hσ
  field_simp
  rw [rr]
  have e1 : σ ^ 2 = 1 := hσ
  rw [s7]
  rw [← hNdef] at hid
  linear_combination (-N) * hid
end Sys
end GTR
