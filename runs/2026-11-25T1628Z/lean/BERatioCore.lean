import Checked.Math.BEMonoMain
import Checked.Math.GelfandRadiiCore

/-! Bonnor–Ebert sphere, `BERatioCore`: the route behind `bonnor_ebert_turning_ratio`. The extrema of the
pressure-confined mass are the zeros of g = 2u − v in the homology variables (`Checked.Math.BEFocus`). The
angle of `Checked.Math.GelfandRatioCore`, measured by an arccosine from the ray of g = 0 on the side where g
keeps its sign (`fcB`, `thB`), is zero and pi at consecutive zeros of g and has the same derivative, two root
seven times the angular momentum over `Nw` t (`thB_deriv`, from the identity `angB_id`), so the segment bounds
of `Checked.Math.GelfandRatioCore.Sys.seg_bounds` hold between consecutive zeros of g (`segB_bounds`). At a
zero of g the weighted norm is thirty-two (u − 1) squared and the mass is the singular value times u squared,
so the quotient of consecutive deviations is minus the exponential of half the advance of log `Nw` times a
factor tending to one (`main`). -/

namespace Checked.Math.BERatioCore
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandRatioCore (le_of_deriv sigma_abs six_sqrt7 Lq_err Dq_err)

/-- The cosine of the angle in the Jordan basis, measured from the ray of `g = 0` on the side `σ`. -/
noncomputable def fcB (σ : ℝ) (U V : ℝ → ℝ) (t : ℝ) : ℝ :=
  σ * (-(6 * (U t - 1)) - 5 * (V t - 2)) / Real.sqrt (8 * Nw (U t - 1) (V t - 2))

/-- The angle. -/
noncomputable def thB (σ : ℝ) (U V : ℝ → ℝ) (t : ℝ) : ℝ := Real.arccos (fcB σ U V t)

theorem eight_N_eq (x y : ℝ) : 8 * Nw x y = (6 * x + 5 * y) ^ 2 + 7 * (2 * x - y) ^ 2 := by
  unfold Nw; ring

/-- The algebraic identity behind the angle's derivative. -/
theorem angB_id (x y : ℝ) :
    28 * (y - 2 * x) * Lq x y =
      (6 * x + 5 * y) * Dq x y - 2 * Nw x y * (6 * ((1 + x) * (-x - y)) + 5 * ((2 + y) * x)) := by
  unfold Lq Dq Nw; ring

theorem fcB_at_zero {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : 0 < σ * -x) :
    σ * (-(6 * x) - 5 * (2 * x)) / Real.sqrt (8 * Nw x (2 * x)) = 1 := by
  have e : 8 * Nw x (2 * x) = (16 * |-x|) ^ 2 := by unfold Nw; rw [mul_pow, sq_abs]; ring
  rw [e, Real.sqrt_sq (by positivity), sigma_abs hσ h]
  rw [div_eq_one_iff_eq (by positivity)]; ring

theorem fcB_at_zero' {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : σ * -x < 0) :
    σ * (-(6 * x) - 5 * (2 * x)) / Real.sqrt (8 * Nw x (2 * x)) = -1 := by
  have h' : 0 < (-σ) * -x := by linarith
  have := fcB_at_zero (σ := -σ) (x := x) (by rw [neg_sq]; exact hσ) h'
  have e : σ * (-(6 * x) - 5 * (2 * x)) / Real.sqrt (8 * Nw x (2 * x)) =
      -((-σ) * (-(6 * x) - 5 * (2 * x)) / Real.sqrt (8 * Nw x (2 * x))) := by ring
  rw [e, this]

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem fcB_cont : ContinuousOn (fcB σ U V) (Ici s0) := by
  intro t ht
  have hN := S.N_pos ht
  have hU := (S.hU t ht).continuousAt
  have hV := (S.hV t ht).continuousAt
  have hNc : ContinuousAt (fun t => Nw (U t - 1) (V t - 2)) t := (S.dN ht).continuousAt
  have hr : Real.sqrt (8 * Nw (U t - 1) (V t - 2)) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  apply ContinuousAt.continuousWithinAt
  unfold fcB
  exact ((continuousAt_const.mul (((continuousAt_const.mul (hU.sub continuousAt_const))).neg.sub
    (continuousAt_const.mul (hV.sub continuousAt_const)))).div ((continuousAt_const.mul hNc).sqrt) hr)

theorem thB_cont : ContinuousOn (thB σ U V) (Ici s0) :=
  Real.continuous_arccos.comp_continuousOn (fcB_cont S)

theorem thB_deriv {σ t : ℝ} (hσ : σ ^ 2 = 1) (ht : t ∈ Ici s0) (hy : 0 < σ * (2 * U t - V t)) :
    HasDerivAt (thB σ U V)
      (2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t)) t := by
  set x := U t - 1 with hx
  set y := V t - 2 with hy'
  set N := Nw x y with hNdef
  have tp := S.tpos ht
  have hN : 0 < N := S.N_pos ht
  set r := Real.sqrt (8 * N) with hr
  have r0 : 0 < r := Real.sqrt_pos.2 (by linarith)
  have rr : r ^ 2 = 8 * N := Real.sq_sqrt (by linarith)
  have s7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have s7p : 0 < Real.sqrt 7 := by positivity
  have hg : 2 * U t - V t = 2 * x - y := by rw [hx, hy']; ring
  have hp : HasDerivAt (fun t => -(6 * (U t - 1)) - 5 * (V t - 2))
      (-(6 * (U t * (3 - U t - V t) / t)) - 5 * (V t * (U t - 1) / t)) t :=
    (((S.hU t ht).sub_const 1).const_mul 6).neg.sub (((S.hV t ht).sub_const 2).const_mul 5)
  have hrd : HasDerivAt (fun t => Real.sqrt (8 * Nw (U t - 1) (V t - 2)))
      (8 * (Dq x y / t) / (2 * r)) t :=
    ((S.dN ht).const_mul 8).sqrt (by rw [← hNdef]; linarith)
  have hf : HasDerivAt (fcB σ U V)
      ((σ * (-(6 * (U t * (3 - U t - V t) / t)) - 5 * (V t * (U t - 1) / t)) * r
        - σ * (-(6 * x) - 5 * y) * (8 * (Dq x y / t) / (2 * r))) / r ^ 2) t := by
    have := (hp.const_mul σ).div hrd r0.ne'
    unfold fcB
    convert this using 1
  have h1f : 1 - fcB σ U V t ^ 2 = (Real.sqrt 7 * (σ * (2 * x - y)) / r) ^ 2 := by
    unfold fcB
    rw [← hr]
    rw [div_pow, div_pow, mul_pow, mul_pow, mul_pow, rr, s7, hσ]
    have := eight_N_eq x y
    field_simp
    linarith
  have hyx : 0 < σ * (2 * x - y) := by rw [← hg]; exact hy
  have hsq : Real.sqrt (1 - fcB σ U V t ^ 2) = Real.sqrt 7 * (σ * (2 * x - y)) / r := by
    rw [h1f]; exact Real.sqrt_sq (by positivity)
  have hne1 : fcB σ U V t ≠ 1 := by
    intro h; have := h1f; rw [h] at this
    have : 0 < (Real.sqrt 7 * (σ * (2 * x - y)) / r) ^ 2 := by positivity
    linarith
  have hne2 : fcB σ U V t ≠ -1 := by
    intro h; have := h1f; rw [h] at this
    have : 0 < (Real.sqrt 7 * (σ * (2 * x - y)) / r) ^ 2 := by positivity
    linarith
  have ha := (Real.hasDerivAt_arccos hne2 hne1).comp t hf
  unfold thB
  refine ha.congr_deriv ?_
  rw [hsq]
  have hU1 : U t = 1 + x := by rw [hx]; ring
  have hV2 : V t = 2 + y := by rw [hy']; ring
  have hid := angB_id x y
  rw [← hNdef] at hid
  clear_value x y N r
  rw [hU1, hV2]
  have hyne : 2 * x - y ≠ 0 := by rintro h; rw [h] at hyx; simp at hyx
  have hσne : σ ≠ 0 := by rintro h; rw [h] at hσ; norm_num at hσ
  field_simp
  rw [rr]
  rw [s7]
  linear_combination (8 * N) * hid

theorem x_ne_of_zeroB {a : ℝ} (ha : a ∈ Ici s0) (hga : 2 * U a - V a = 0) : U a - 1 ≠ 0 := by
  intro h; exact (S.at_zero ha hga).2.1 (by linarith)

/-- At the left end of a segment on the side `σ`, `σ (1 − u) > 0`. -/
theorem sideB_left {a b σ : ℝ} (ha : a ∈ Ici s0) (hab : a < b) (hga : 2 * U a - V a = 0)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (2 * U t - V t)) : 0 < σ * -(U a - 1) := by
  have ap := S.tpos ha
  have hUa := (S.UV_pos ha).1
  obtain ⟨-, hU1, hdv⟩ := S.at_zero ha hga
  have hd : HasDerivAt (fun t => σ * (2 * U t - V t)) (σ * (8 * U a * (1 - U a) / a)) a := by
    have := (S.dg ha).const_mul σ; rw [hdv] at this; exact this
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | heq
  · have hneg : σ * (8 * U a * (1 - U a) / a) < 0 := by
      have : σ * (8 * U a * (1 - U a) / a) = 8 * U a * (σ * -(U a - 1)) / a := by ring
      rw [this]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hlt) ap
    have ev := Checked.Math.GelfandExtremaMain.right_lt hd hneg
    have ev2 : ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a b := Ioo_mem_nhdsGT hab
    obtain ⟨t, h1, h2⟩ := (ev.and ev2).exists
    have := hsg t h2
    simp only [hga, mul_zero] at h1
    linarith
  · have hσ0 : σ ≠ 0 := by
      intro h0; obtain ⟨t, ht⟩ := nonempty_Ioo.2 hab; have := hsg t ht; rw [h0] at this; simp at this
    rcases mul_eq_zero.1 heq with h | h
    · exact hσ0 h
    · exact hU1 (by linarith)

/-- At the right end of a segment on the side `σ`, `σ (1 − u) < 0`. -/
theorem sideB_right {a b σ : ℝ} (ha : a ∈ Ici s0) (hab : a < b) (hgb : 2 * U b - V b = 0)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (2 * U t - V t)) : σ * -(U b - 1) < 0 := by
  have hb : b ∈ Ici s0 := mem_Ici.2 (le_trans ha hab.le)
  have bp := S.tpos hb
  have hUb := (S.UV_pos hb).1
  obtain ⟨-, hU1, hdv⟩ := S.at_zero hb hgb
  have hd : HasDerivAt (fun t => σ * (2 * U t - V t)) (σ * (8 * U b * (1 - U b) / b)) b := by
    have := (S.dg hb).const_mul σ; rw [hdv] at this; exact this
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | heq
  · have hpos : 0 < σ * (8 * U b * (1 - U b) / b) := by
      have : σ * (8 * U b * (1 - U b) / b) = 8 * U b * (σ * -(U b - 1)) / b := by ring
      rw [this]; exact div_pos (mul_pos (by positivity) hlt) bp
    have ev := Checked.Math.GelfandExtremaMain.left_lt hd hpos
    have ev2 : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b := Ioo_mem_nhdsLT hab
    obtain ⟨t, h1, h2⟩ := (ev.and ev2).exists
    have := hsg t h2
    simp only [hgb, mul_zero] at h1
    linarith
  · have hσ0 : σ ≠ 0 := by
      intro h0; obtain ⟨t, ht⟩ := nonempty_Ioo.2 hab; have := hsg t ht; rw [h0] at this; simp at this
    rcases mul_eq_zero.1 heq.symm with h | h
    · exact hσ0 h
    · exact hU1 (by linarith)

theorem thB_left {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hga : 2 * U a - V a = 0)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (2 * U t - V t)) : thB σ U V a = 0 := by
  unfold thB fcB
  have h := fcB_at_zero hσ (sideB_left S ha hab hga hsg)
  have e : V a - 2 = 2 * (U a - 1) := by linarith
  rw [e, h, Real.arccos_one]

theorem thB_right {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hgb : 2 * U b - V b = 0)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (2 * U t - V t)) : thB σ U V b = Real.pi := by
  unfold thB fcB
  have h := fcB_at_zero' hσ (sideB_right S ha hab hgb hsg)
  have e : V b - 2 = 2 * (U b - 1) := by linarith
  rw [e, h, Real.arccos_neg_one]

end Sys
end Checked.Math.BERatioCore

namespace Checked.Math.BERatioCore
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandRatioCore (le_of_deriv sigma_abs six_sqrt7 Lq_err Dq_err)

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

/-- Bounds on one segment between consecutive zeros of `g`: the angle advances by pi, which bounds the
advance of log t, and log Nw advances at rate −1 up to `36 √Nw`. -/
theorem segB_bounds {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hya : 2 * U a - V a = 0)
    (hyb : 2 * U b - V b = 0) (hsg : ∀ t ∈ Ioo a b, 0 < σ * (2 * U t - V t)) :
    (Real.sqrt 7 / 2 - 16 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ≤ Real.pi ∧
    Real.pi ≤ (Real.sqrt 7 / 2 + 16 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ∧
    -(1 + 36 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ≤
      Real.log (Nw (U b - 1) (V b - 2)) - Real.log (Nw (U a - 1) (V a - 2)) ∧
    Real.log (Nw (U b - 1) (V b - 2)) - Real.log (Nw (U a - 1) (V a - 2)) ≤
      -(1 - 36 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) := by
  set ε := Real.sqrt (Nw (U a - 1) (V a - 2)) with hε
  have hIcc : ∀ t ∈ Icc a b, t ∈ Ici s0 := fun t ht => mem_Ici.2 (le_trans ha ht.1)
  have hIoo : ∀ t ∈ Ioo a b, t ∈ Ici s0 := fun t ht => hIcc t (Ioo_subset_Icc_self ht)
  have th_c : ContinuousOn (thB σ U V) (Icc a b) := (thB_cont S).mono (fun t ht => hIcc t ht)
  have lc := Checked.Math.GelfandRatioCore.Sys.log_cont S (b := b) ha
  have lN := Checked.Math.GelfandRatioCore.Sys.logN_cont S (b := b) ha
  have tha := thB_left S hσ ha hab hya hsg
  have thb := thB_right S hσ ha hab hyb hsg
  have s7 := six_sqrt7
  -- pointwise facts inside
  have inside : ∀ t ∈ Ioo a b, 0 < t ∧ 0 < Nw (U t - 1) (V t - 2) ∧
      Real.sqrt (Nw (U t - 1) (V t - 2)) ≤ ε ∧
      |Lq (U t - 1) (V t - 2) - Nw (U t - 1) (V t - 2) / 4| ≤
        3 * Nw (U t - 1) (V t - 2) * Real.sqrt (Nw (U t - 1) (V t - 2)) ∧
      |Dq (U t - 1) (V t - 2) + Nw (U t - 1) (V t - 2)| ≤
        36 * Nw (U t - 1) (V t - 2) * Real.sqrt (Nw (U t - 1) (V t - 2)) := fun t ht =>
    ⟨S.tpos (hIoo t ht), S.N_pos (hIoo t ht), Checked.Math.GelfandRatioCore.Sys.sqrtN_le S ha ht.1.le, Lq_err _ _, Dq_err _ _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := le_of_deriv (G := fun t => thB σ U V t - (Real.sqrt 7 / 2 - 16 * ε) * Real.log t)
      (G' := fun t => 2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t) -
        (Real.sqrt 7 / 2 - 16 * ε) * t⁻¹) hab.le (th_c.sub (continuousOn_const.mul lc))
      (fun t ht => (thB_deriv S hσ (hIoo t ht) (hsg t ht)).sub
        ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
      (fun t ht => by
        obtain ⟨tp, Np, sl, hL, -⟩ := inside t ht
        have hL1 := (abs_le.1 hL).1
        have e : 2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t) -
            (Real.sqrt 7 / 2 - 16 * ε) * t⁻¹ =
            (2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) - (Real.sqrt 7 / 2 - 16 * ε) * Nw (U t - 1) (V t - 2)) /
              (Nw (U t - 1) (V t - 2) * t) := by field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        have s7p : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
        have hr : 0 ≤ Real.sqrt (Nw (U t - 1) (V t - 2)) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 7),
          mul_le_mul_of_nonneg_left sl Np.le, mul_nonneg Np.le hr,
          mul_le_mul_of_nonneg_right s7 (mul_nonneg Np.le hr)])
    simp only [tha, thb] at this
    linarith
  · have := le_of_deriv (G := fun t => (Real.sqrt 7 / 2 + 16 * ε) * Real.log t - thB σ U V t)
      (G' := fun t => (Real.sqrt 7 / 2 + 16 * ε) * t⁻¹ -
        2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t)) hab.le
      ((continuousOn_const.mul lc).sub th_c)
      (fun t ht => ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _).sub
        (thB_deriv S hσ (hIoo t ht) (hsg t ht)))
      (fun t ht => by
        obtain ⟨tp, Np, sl, hL, -⟩ := inside t ht
        have hL1 := (abs_le.1 hL).2
        have e : (Real.sqrt 7 / 2 + 16 * ε) * t⁻¹ -
            2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t) =
            ((Real.sqrt 7 / 2 + 16 * ε) * Nw (U t - 1) (V t - 2) - 2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2)) /
              (Nw (U t - 1) (V t - 2) * t) := by field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        have s7p : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
        have hr : 0 ≤ Real.sqrt (Nw (U t - 1) (V t - 2)) := Real.sqrt_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt 7),
          mul_le_mul_of_nonneg_left sl Np.le, mul_nonneg Np.le hr,
          mul_le_mul_of_nonneg_right s7 (mul_nonneg Np.le hr)])
    simp only [tha, thb] at this
    linarith
  · have := le_of_deriv (G := fun t => Real.log (Nw (U t - 1) (V t - 2)) + (1 + 36 * ε) * Real.log t)
      (G' := fun t => Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2) + (1 + 36 * ε) * t⁻¹) hab.le
      (lN.add (continuousOn_const.mul lc))
      (fun t ht => (Checked.Math.GelfandRatioCore.Sys.logN_deriv S (hIoo t ht)).add ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
      (fun t ht => by
        obtain ⟨tp, Np, sl, -, hD⟩ := inside t ht
        have hD1 := (abs_le.1 hD).1
        have e : Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2) + (1 + 36 * ε) * t⁻¹ =
            (Dq (U t - 1) (V t - 2) + (1 + 36 * ε) * Nw (U t - 1) (V t - 2)) / (Nw (U t - 1) (V t - 2) * t) := by
          field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left sl Np.le])
    linarith
  · have := le_of_deriv (G := fun t => -Real.log (Nw (U t - 1) (V t - 2)) - (1 - 36 * ε) * Real.log t)
      (G' := fun t => -(Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2)) - (1 - 36 * ε) * t⁻¹) hab.le
      (lN.neg.sub (continuousOn_const.mul lc))
      (fun t ht => (Checked.Math.GelfandRatioCore.Sys.logN_deriv S (hIoo t ht)).neg.sub ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
      (fun t ht => by
        obtain ⟨tp, Np, sl, -, hD⟩ := inside t ht
        have hD1 := (abs_le.1 hD).2
        have e : -(Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2)) - (1 - 36 * ε) * t⁻¹ =
            (-Dq (U t - 1) (V t - 2) - (1 - 36 * ε) * Nw (U t - 1) (V t - 2)) / (Nw (U t - 1) (V t - 2) * t) := by
          field_simp
        rw [e]
        apply div_nonneg _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left sl Np.le])
    linarith

end Sys
end Checked.Math.BERatioCore

namespace Checked.Math.BERatioCore
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (U V Hyp hyp_of U_deriv V_deriv phi_neg U_pos right_gt right_lt left_lt)

/-- u v³ along the system: its logarithmic derivative is g = 2u − v. -/
theorem P_deriv {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0) {t : ℝ} (ht : t ∈ Ici s0) :
    HasDerivAt (fun t => U t * V t ^ 3) (U t * V t ^ 3 * (2 * U t - V t) / t) t := by
  have tp := S.tpos ht
  have h := (S.hU t ht).mul (((S.hV t ht).mul (S.hV t ht)).mul (S.hV t ht))
  have e : (fun t => U t * V t ^ 3) = (fun t => U t * (V t * V t * V t)) := by funext s; ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Inside a segment where g keeps one weak sign, g does not vanish (transversality). -/
theorem no_zero_insideB {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0) {a b σ t : ℝ} (ha : a ∈ Ici s0)
    (ht : t ∈ Ioo a b) (hnn : ∀ t ∈ Ioo a b, 0 ≤ σ * (2 * U t - V t)) (hσ : σ ^ 2 = 1) :
    2 * U t - V t ≠ 0 := by
  intro hg
  have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
  have tp := S.tpos ht0
  have hUt := (S.UV_pos ht0).1
  obtain ⟨-, hU1, hdv⟩ := S.at_zero ht0 hg
  have hd : HasDerivAt (fun s => σ * (2 * U s - V s)) (σ * (8 * U t * (1 - U t) / t)) t := by
    have := (S.dg ht0).const_mul σ; rw [hdv] at this; exact this
  have hσ0 : σ ≠ 0 := by rintro h; rw [h] at hσ; norm_num at hσ
  have hd0 : σ * (8 * U t * (1 - U t) / t) ≠ 0 := by
    apply mul_ne_zero hσ0; apply div_ne_zero _ tp.ne'
    apply mul_ne_zero (by positivity); intro h; apply hU1; linarith
  have hval : σ * (2 * U t - V t) = 0 := by rw [hg]; ring
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · obtain ⟨s, h1, h2⟩ := ((right_lt hd hneg).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hnn s ⟨ht.1.trans h2.1, h2.2⟩
    simp only [hval] at h1; linarith
  · obtain ⟨s, h1, h2⟩ := ((left_lt hd hpos).and (Ioo_mem_nhdsLT ht.1)).exists
    have := hnn s ⟨h2.1, h2.2.trans ht.2⟩
    simp only [hval] at h1; linarith

/-- On a segment where u v³ decreases, g < 0 inside. -/
theorem neg_of_antiP {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0) {a b : ℝ} (ha : a ∈ Ici s0)
    (hanti : StrictAntiOn (fun t => U t * V t ^ 3) (Icc a b)) :
    ∀ t ∈ Ioo a b, 0 < (-1 : ℝ) * (2 * U t - V t) := by
  have hnn : ∀ t ∈ Ioo a b, 0 ≤ (-1 : ℝ) * (2 * U t - V t) := by
    intro t ht
    have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
    have tp := S.tpos ht0
    obtain ⟨hu, hv⟩ := S.UV_pos ht0
    by_contra hc
    push Not at hc
    have hd := P_deriv S ht0
    have hpos : 0 < U t * V t ^ 3 * (2 * U t - V t) / t := by
      apply div_pos _ tp; apply mul_pos (by positivity); linarith
    obtain ⟨s, h1, h2⟩ := ((right_gt hd hpos).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hanti ⟨ht.1.le, ht.2.le⟩ ⟨(ht.1.trans h2.1).le, h2.2.le⟩ h2.1
    simp only at h1 this
    linarith
  intro t ht
  rcases (hnn t ht).lt_or_eq with h | h
  · exact h
  · exact absurd (by linarith : 2 * U t - V t = 0) (no_zero_insideB S ha ht hnn (by norm_num))

/-- On a segment where u v³ increases, g > 0 inside. -/
theorem pos_of_monoP {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0) {a b : ℝ} (ha : a ∈ Ici s0)
    (hmono : StrictMonoOn (fun t => U t * V t ^ 3) (Icc a b)) :
    ∀ t ∈ Ioo a b, 0 < (1 : ℝ) * (2 * U t - V t) := by
  have hnn : ∀ t ∈ Ioo a b, 0 ≤ (1 : ℝ) * (2 * U t - V t) := by
    intro t ht
    have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
    have tp := S.tpos ht0
    obtain ⟨hu, hv⟩ := S.UV_pos ht0
    by_contra hc
    push Not at hc
    have hd := P_deriv S ht0
    have hneg : U t * V t ^ 3 * (2 * U t - V t) / t < 0 := by
      apply div_neg_of_neg_of_pos _ tp; apply mul_neg_of_pos_of_neg (by positivity); linarith
    obtain ⟨s, h1, h2⟩ := ((right_lt hd hneg).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hmono ⟨ht.1.le, ht.2.le⟩ ⟨(ht.1.trans h2.1).le, h2.2.le⟩ h2.1
    simp only at h1 this
    linarith
  intro t ht
  rcases (hnn t ht).lt_or_eq with h | h
  · exact h
  · exact absurd (by linarith : 2 * U t - V t = 0) (no_zero_insideB S ha ht hnn (by norm_num))

/-- The mass decreases where u v³ decreases. -/
theorem P_anti_of_M {w φ : ℝ → ℝ} (E : Hyp w φ) {a b : ℝ} (ha : 0 < a)
    (h : StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc a b)) :
    StrictAntiOn (fun t => U w φ t * V φ t ^ 3) (Icc a b) := by
  intro s hs t ht hst
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  obtain ⟨e1, p1⟩ := Checked.Math.BEHMain.mass_sq (w := w) hs0 (phi_neg E hs0)
  obtain ⟨e2, p2⟩ := Checked.Math.BEHMain.mass_sq (w := w) ht0 (phi_neg E ht0)
  have hm := h hs ht hst
  simp only at hm ⊢
  change _ = U w φ s * V φ s ^ 3 at e1
  change _ = U w φ t * V φ t ^ 3 at e2
  rw [← e1, ← e2]
  have hpi : 0 < 4 * Real.pi := by positivity
  exact mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hm p2.le two_ne_zero) hpi

theorem P_mono_of_M {w φ : ℝ → ℝ} (E : Hyp w φ) {a b : ℝ} (ha : 0 < a)
    (h : StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) (Icc a b)) :
    StrictMonoOn (fun t => U w φ t * V φ t ^ 3) (Icc a b) := by
  intro s hs t ht hst
  have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  obtain ⟨e1, p1⟩ := Checked.Math.BEHMain.mass_sq (w := w) hs0 (phi_neg E hs0)
  obtain ⟨e2, p2⟩ := Checked.Math.BEHMain.mass_sq (w := w) ht0 (phi_neg E ht0)
  have hm := h hs ht hst
  simp only at hm ⊢
  change _ = U w φ s * V φ s ^ 3 at e1
  change _ = U w φ t * V φ t ^ 3 at e2
  rw [← e1, ← e2]
  have hpi : 0 < 4 * Real.pi := by positivity
  exact mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hm p1.le two_ne_zero) hpi

/-- At a zero of g the mass is the singular value times u squared. -/
theorem M_at_zero {w φ : ℝ → ℝ} (E : Hyp w φ) {t : ℝ} (ht : 0 < t) (hg : 2 * U w φ t - V φ t = 0) :
    t ^ 2 * (-φ t) * Real.exp (w t / 2) / Real.sqrt (4 * Real.pi) - Real.sqrt (2 / Real.pi) =
      Real.sqrt (2 / Real.pi) * (U w φ t ^ 2 - 1) := by
  obtain ⟨e1, p1⟩ := Checked.Math.BEHMain.mass_sq (w := w) ht (phi_neg E ht)
  change _ = U w φ t * V φ t ^ 3 at e1
  have hv : V φ t = 2 * U w φ t := by linarith
  have hu := U_pos E ht
  have hc := Checked.Math.BEAllMain.c_sq
  have c0 : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hpi : 0 < 4 * Real.pi := by positivity
  have h2 : (t ^ 2 * (-φ t) * Real.exp (w t / 2) / Real.sqrt (4 * Real.pi)) ^ 2 =
      (Real.sqrt (2 / Real.pi) * U w φ t ^ 2) ^ 2 := by
    have : (t ^ 2 * (-φ t) * Real.exp (w t / 2) / Real.sqrt (4 * Real.pi)) ^ 2 * (4 * Real.pi) =
        (Real.sqrt (2 / Real.pi) * U w φ t ^ 2) ^ 2 * (4 * Real.pi) := by
      rw [e1, hv]
      have e : (Real.sqrt (2 / Real.pi) * U w φ t ^ 2) ^ 2 * (4 * Real.pi) =
          (Real.sqrt (2 / Real.pi) ^ 2 * (4 * Real.pi)) * U w φ t ^ 4 := by ring
      rw [e, hc]; ring
    exact mul_right_cancel₀ hpi.ne' this
  have hm := (pow_left_inj₀ p1.le (by positivity) two_ne_zero).1 h2
  rw [hm]; ring

theorem q_eq32 {xa xb Na Nb : ℝ} (hNa : Na = 32 * xa ^ 2) (hNb : Nb = 32 * xb ^ 2) (hs : xb * xa < 0) :
    xb / xa = -Real.exp ((Real.log Nb - Real.log Na) / 2) := by
  have ha : xa ≠ 0 := by rintro h; rw [h] at hs; simp at hs
  have hb : xb ≠ 0 := by rintro h; rw [h] at hs; simp at hs
  have hNa' : 0 < Na := by rw [hNa]; positivity
  have hNb' : 0 < Nb := by rw [hNb]; positivity
  have hq : xb / xa < 0 := by
    have : xb / xa = xb * xa / xa ^ 2 := by field_simp
    rw [this]; exact div_neg_of_neg_of_pos hs (by positivity)
  have e1 : Real.exp ((Real.log Nb - Real.log Na) / 2) ^ 2 = (xb / xa) ^ 2 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * ((Real.log Nb - Real.log Na) / 2) =
      Real.log Nb - Real.log Na by push_cast; ring, Real.exp_sub, Real.exp_log hNa', Real.exp_log hNb',
      hNa, hNb]
    field_simp
  have hp := Real.exp_pos ((Real.log Nb - Real.log Na) / 2)
  nlinarith [sq_nonneg (Real.exp ((Real.log Nb - Real.log Na) / 2) + xb / xa)]

/-- A continuous function with opposite strict signs on the two sides of a point vanishes there. -/
theorem zero_between {g : ℝ → ℝ} {a z b σ : ℝ} (haz : a < z) (hzb : z < b) (hc : ContinuousAt g z)
    (hl : ∀ t ∈ Ioo a z, 0 < σ * g t) (hr : ∀ t ∈ Ioo z b, 0 < -σ * g t) : g z = 0 := by
  by_contra h
  rcases lt_or_gt_of_ne h with hneg | hpos
  · have ev : ∀ᶠ t in 𝓝 z, g t < 0 := hc.eventually (Iio_mem_nhds hneg)
    obtain ⟨t, h1, h2⟩ := ((ev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT haz)).exists
    obtain ⟨t', h1', h2'⟩ := ((ev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hzb)).exists
    have a1 := hl t h2
    have a2 := hr t' h2'
    nlinarith
  · have ev : ∀ᶠ t in 𝓝 z, 0 < g t := hc.eventually (Ioi_mem_nhds hpos)
    obtain ⟨t, h1, h2⟩ := ((ev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT haz)).exists
    obtain ⟨t', h1', h2'⟩ := ((ev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hzb)).exists
    have a1 := hl t h2
    have a2 := hr t' h2'
    nlinarith

theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) <
          ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) / Real.sqrt (4 * Real.pi)) ∧
      Tendsto (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) atTop
        (𝓝 (Real.sqrt (2 / Real.pi))) ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
        (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi))) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) := by
  obtain ⟨ξ, hm, hT, hz0lo, hz0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono⟩ :=
    Checked.Math.BEMonoMain.main w φ hw hφ0 hφ h0
  refine ⟨ξ, hm, hT, hz0lo, hz0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, ?_⟩
  have E := hyp_of hw hφ0 hφ
  obtain ⟨r1, r2, r3⟩ := Checked.Math.BEAllMain.restrict 300000 hw hφ0 hφ
  obtain ⟨-, su, sv, -⟩ := Checked.Math.BEState300.state300 300000 le_rfl w φ r1 r2 r3 h0
  obtain ⟨N0le, N0pos⟩ := Checked.Math.BEAllMain.N0_bounds su sv
  have S : Sys (U w φ) (V φ) 300000 :=
    ⟨by norm_num, fun t ht => U_deriv E (by linarith [mem_Ici.1 ht]),
      fun t ht => V_deriv E (by linarith [mem_Ici.1 ht]), le_trans N0le (by norm_num), N0pos⟩
  have ξpos : ∀ n, 0 < ξ n := fun n =>
    lt_of_lt_of_le (by norm_num at hz0lo; linarith) (hm.monotone (Nat.zero_le n))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hT.eventually (eventually_ge_atTop (300000 : ℝ)))
  have hKi : ∀ k, K ≤ k → ξ k ∈ Ici (300000 : ℝ) := fun k hk => mem_Ici.2 (hK k hk)
  -- the sign of g on each segment from K on
  have side : ∀ k, K ≤ k → ∀ t ∈ Ioo (ξ k) (ξ (k + 1)),
      0 < (-1 : ℝ) ^ (k + 1) * (2 * U w φ t - V φ t) := by
    intro k hk
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · have e : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [e]
      exact neg_of_antiP S (hKi _ hk) (P_anti_of_M E (ξpos _) (hanti m))
    · have e : (-1 : ℝ) ^ (2 * m + 1 + 1) = 1 := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]; norm_num
      rw [e]
      exact pos_of_monoP S (hKi _ hk) (P_mono_of_M E (ξpos _) (hmono m))
  -- the extrema from K + 1 on are zeros of g
  have hgz : ∀ n, K + 1 ≤ n → 2 * U w φ (ξ n) - V φ (ξ n) = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : K ≤ k := by omega
    have hc : ContinuousAt (fun t => 2 * U w φ t - V φ t) (ξ (k + 1)) :=
      (S.dg (hKi (k + 1) (by omega))).continuousAt
    exact zero_between (g := fun t => 2 * U w φ t - V φ t) (σ := (-1 : ℝ) ^ (k + 1))
      (hm (Nat.lt_succ_self k)) (hm (Nat.lt_succ_self (k + 1))) hc (side k hk)
      (fun t ht => by
        have := side (k + 1) (by omega) t ht
        rw [show (-1 : ℝ) ^ (k + 1 + 1) = -(-1) ^ (k + 1) by ring] at this
        exact this)
  have B : ∀ k, K + 1 ≤ k →
      (Real.sqrt 7 / 2 - 16 * Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2))) *
        (Real.log (ξ (k + 1)) - Real.log (ξ k)) ≤ Real.pi ∧
      Real.pi ≤ (Real.sqrt 7 / 2 + 16 * Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2))) *
        (Real.log (ξ (k + 1)) - Real.log (ξ k)) ∧
      -(1 + 36 * Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2))) *
          (Real.log (ξ (k + 1)) - Real.log (ξ k)) ≤
        Real.log (Nw (U w φ (ξ (k + 1)) - 1) (V φ (ξ (k + 1)) - 2)) -
          Real.log (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) ∧
      Real.log (Nw (U w φ (ξ (k + 1)) - 1) (V φ (ξ (k + 1)) - 2)) -
          Real.log (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) ≤
        -(1 - 36 * Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2))) *
          (Real.log (ξ (k + 1)) - Real.log (ξ k)) := fun k hk =>
    Checked.Math.BERatioCore.Sys.segB_bounds S (neg_one_pow_sq (k + 1)) (hKi k (by omega))
      (hm (Nat.lt_succ_self k)) (hgz k hk) (hgz (k + 1) (by omega)) (side k (by omega))
  set ε : ℕ → ℝ := fun k => Real.sqrt (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) with hεdef
  set L : ℕ → ℝ := fun k => Real.log (ξ (k + 1)) - Real.log (ξ k) with hLdef
  set D : ℕ → ℝ := fun k => Real.log (Nw (U w φ (ξ (k + 1)) - 1) (V φ (ξ (k + 1)) - 2)) -
    Real.log (Nw (U w φ (ξ k) - 1) (V φ (ξ k) - 2)) with hDdef
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (S.N_tendsto.comp hT)
    rw [Real.sqrt_zero] at this
    exact this
  have hD := Checked.Math.GelfandRatioCore.lim_D (ε := ε) (L := L) (D := D) (K := K + 1) hε
    (fun k hk => (B k hk).1) (fun k hk => (B k hk).2.1) (fun k hk => (B k hk).2.2.1)
    (fun k hk => (B k hk).2.2.2)
  have hL := Checked.Math.GelfandRadiiCore.lim_L (ε := ε) (L := L) (K := K + 1) hε
    (fun k hk => (B k hk).1) (fun k hk => (B k hk).2.1)
  have hratio : ∀ k, ξ (k + 1) / ξ k = Real.exp (L k) := by
    intro k
    simp only [hLdef]
    rw [Real.exp_sub, Real.exp_log (ξpos _), Real.exp_log (ξpos _)]
  refine ⟨?_, ?_⟩
  · have := ((Real.continuous_exp.tendsto _).comp hL)
    have e : Real.pi / (Real.sqrt 7 / 2) = 2 * Real.pi / Real.sqrt 7 := by
      have : Real.sqrt 7 ≠ 0 := by positivity
      field_simp
    rw [e] at this
    refine this.congr' (Eventually.of_forall fun k => ?_)
    exact (hratio k).symm
  -- the quotient of deviations
  set c := Real.sqrt (2 / Real.pi) with hc
  have c0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have dev : ∀ n, K + 1 ≤ n →
      ξ n ^ 2 * (-φ (ξ n)) * Real.exp (w (ξ n) / 2) / Real.sqrt (4 * Real.pi) - c =
        c * (U w φ (ξ n) ^ 2 - 1) := fun n hn => M_at_zero E (ξpos n) (hgz n hn)
  have Nz : ∀ n, K + 1 ≤ n → Nw (U w φ (ξ n) - 1) (V φ (ξ n) - 2) = 32 * (U w φ (ξ n) - 1) ^ 2 :=
    fun n hn => (S.at_zero (hKi n (by omega)) (hgz n hn)).1
  have alt : ∀ n, (ξ (n + 1) ^ 2 * (-φ (ξ (n + 1))) * Real.exp (w (ξ (n + 1)) / 2) /
      Real.sqrt (4 * Real.pi) - c) *
      (ξ n ^ 2 * (-φ (ξ n)) * Real.exp (w (ξ n) / 2) / Real.sqrt (4 * Real.pi) - c) < 0 := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have a1 := (h2 m).1
      have a2 := (h2 m).2
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    · have a1 := (h2 m).1
      have a2 := (h2 (m + 1)).2
      have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [e] at a2
      exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hE : Tendsto (fun k => -Real.exp (D k / 2)) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) :=
    Checked.Math.GelfandRatioCore.lim_q (D := D) (q := fun k => -Real.exp (D k / 2)) (K := 0) hD
      (fun k _ => rfl)
  have hU : Tendsto (fun k => U w φ (ξ k)) atTop (𝓝 1) := S.U_tendsto.comp hT
  have hF : Tendsto (fun k => (U w φ (ξ (k + 1)) + 1) / (U w φ (ξ k) + 1)) atTop (𝓝 ((1 + 1) / (1 + 1))) :=
    (((hU.comp (tendsto_add_atTop_nat 1)).add_const 1).div (hU.add_const 1) (by norm_num))
  rw [show ((1 : ℝ) + 1) / (1 + 1) = 1 by norm_num] at hF
  have hP := hE.mul hF
  rw [mul_one] at hP
  refine hP.congr' ?_
  filter_upwards [eventually_ge_atTop (K + 1)] with k hk
  have hu0 : 0 < U w φ (ξ k) := U_pos E (ξpos k)
  have hu1 : 0 < U w φ (ξ (k + 1)) := U_pos E (ξpos (k + 1))
  have hs : (U w φ (ξ (k + 1)) - 1) * (U w φ (ξ k) - 1) < 0 := by
    have a := alt k
    rw [dev (k + 1) (by omega), dev k hk] at a
    have e : c * (U w φ (ξ (k + 1)) ^ 2 - 1) * (c * (U w φ (ξ k) ^ 2 - 1)) =
        ((U w φ (ξ (k + 1)) - 1) * (U w φ (ξ k) - 1)) *
          (c ^ 2 * (U w φ (ξ (k + 1)) + 1) * (U w φ (ξ k) + 1)) := by ring
    rw [e] at a
    have hpos : 0 < c ^ 2 * (U w φ (ξ (k + 1)) + 1) * (U w φ (ξ k) + 1) := by positivity
    by_contra hc'
    push Not at hc'
    have := mul_nonneg hc' hpos.le
    linarith
  have hx0 : U w φ (ξ k) - 1 ≠ 0 := by rintro h; rw [h] at hs; simp at hs
  have hq := q_eq32 (Nz k hk) (Nz (k + 1) (by omega)) hs
  rw [dev (k + 1) (by omega), dev k hk]
  change -Real.exp (D k / 2) * _ = _
  simp only [hDdef]
  rw [← hq]
  rw [mul_div_mul_left _ _ c0.ne']
  have h1 : U w φ (ξ k) + 1 ≠ 0 := by positivity
  have h2' : U w φ (ξ k) ^ 2 - 1 ≠ 0 := by
    rw [show U w φ (ξ k) ^ 2 - 1 = (U w φ (ξ k) - 1) * (U w φ (ξ k) + 1) by ring]
    exact mul_ne_zero hx0 h1
  field_simp
  ring

end Checked.Math.BERatioCore

#print axioms Checked.Math.BERatioCore.main
