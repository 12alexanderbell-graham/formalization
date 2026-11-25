import Checked.Math.BEFocus
import Checked.Math.GelfandExtremaMain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

theorem abs_x_le (x y : ℝ) : |x| ≤ Real.sqrt (Nw x y) := Real.abs_le_sqrt (x_sq_le_Nw x y)

/-- The angular momentum is a quarter of `Nw` up to a cubic term. -/
theorem Lq_err (x y : ℝ) : |Lq x y - Nw x y / 4| ≤ 3 * Nw x y * Real.sqrt (Nw x y) := by
  have e : Lq x y - Nw x y / 4 = x * y * (2 * x + y) := by unfold Lq Nw; ring
  rw [e]
  have hx := abs_x_le x y
  have hy := y_abs_le x y
  have hr := Real.sqrt_nonneg (Nw x y)
  have hN : Real.sqrt (Nw x y) ^ 2 = Nw x y := Real.sq_sqrt (Checked.Math.BEOCell.Nw_nonneg x y)
  have h3 : |2 * x + y| ≤ 3 * Real.sqrt (Nw x y) := by
    calc |2 * x + y| ≤ |2 * x| + |y| := abs_add_le _ _
      _ = 2 * |x| + |y| := by rw [abs_mul, abs_two]
      _ ≤ 3 * Real.sqrt (Nw x y) := by linarith
  rw [abs_mul, abs_mul]
  calc |x| * |y| * |2 * x + y| ≤ Real.sqrt (Nw x y) * Real.sqrt (Nw x y) * (3 * Real.sqrt (Nw x y)) := by
        apply mul_le_mul (mul_le_mul hx hy (abs_nonneg _) hr) h3 (abs_nonneg _) (by positivity)
    _ = 3 * Nw x y * Real.sqrt (Nw x y) := by linear_combination 3 * Real.sqrt (Nw x y) * hN

/-- `Dq` is `-Nw` up to a cubic term. -/
theorem Dq_err (x y : ℝ) : |Dq x y + Nw x y| ≤ 36 * Nw x y * Real.sqrt (Nw x y) := by
  have e : Dq x y + Nw x y = -(4 * x) * (4 * x ^ 2 + 4 * x * y - y ^ 2) := by unfold Dq; ring
  rw [e]
  have hx := abs_x_le x y
  have hy := y_abs_le x y
  have hr := Real.sqrt_nonneg (Nw x y)
  have hN : Real.sqrt (Nw x y) ^ 2 = Nw x y := Real.sq_sqrt (Checked.Math.BEOCell.Nw_nonneg x y)
  have hxx : x ^ 2 ≤ Nw x y := x_sq_le_Nw x y
  have hyy : y ^ 2 ≤ Nw x y := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2; linarith
  have hxy : |x * y| ≤ Nw x y := by
    rw [abs_mul]
    have := mul_le_mul hx hy (abs_nonneg _) hr
    nlinarith
  have h9 : |4 * x ^ 2 + 4 * x * y - y ^ 2| ≤ 9 * Nw x y := by
    have a1 := abs_le.1 hxy
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_neg, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
  calc 4 * |x| * |4 * x ^ 2 + 4 * x * y - y ^ 2| ≤ 4 * Real.sqrt (Nw x y) * (9 * Nw x y) := by
        apply mul_le_mul (by linarith) h9 (abs_nonneg _) (by positivity)
    _ = 36 * Nw x y * Real.sqrt (Nw x y) := by ring

end GTR

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
namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

/-- A function continuous on `[a, b]` with a nonnegative derivative inside does not decrease. -/
theorem le_of_deriv {G G' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn G (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt G (G' t) t) (hp : ∀ t ∈ Ioo a b, 0 ≤ G' t) : G a ≤ G b := by
  have hm : MonotoneOn G (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    · rw [interior_Icc]; exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro t ht; rw [(hd t ht).deriv]; exact hp t ht
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem sigma_abs {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : 0 < σ * x) : |x| = σ * x := by
  have : |σ| = 1 := by
    have := sq_abs σ; rw [hσ] at this
    nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1), sq_nonneg (|σ| + 1)]
  rw [← abs_of_pos h, abs_mul, this, one_mul]

theorem fc_at_zero {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : 0 < σ * x) :
    σ * (4 * x + 0) / Real.sqrt (2 * Nw x 0) = 1 := by
  have e : 2 * Nw x 0 = (4 * |x|) ^ 2 := by unfold Nw; rw [mul_pow, sq_abs]; ring
  rw [e, Real.sqrt_sq (by positivity), sigma_abs hσ h]
  rw [div_eq_one_iff_eq (by positivity)]; ring

theorem fc_at_zero' {σ x : ℝ} (hσ : σ ^ 2 = 1) (h : σ * x < 0) :
    σ * (4 * x + 0) / Real.sqrt (2 * Nw x 0) = -1 := by
  have h' : 0 < (-σ) * x := by linarith
  have := fc_at_zero (σ := -σ) (x := x) (by rw [neg_sq]; exact hσ) h'
  have e : σ * (4 * x + 0) / Real.sqrt (2 * Nw x 0) = -((-σ) * (4 * x + 0) / Real.sqrt (2 * Nw x 0)) := by
    ring
  rw [e, this]

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem N_le_of {a t : ℝ} (ha : a ∈ Ici s0) (hat : a ≤ t) :
    Nw (U t - 1) (V t - 2) ≤ Nw (U a - 1) (V a - 2) :=
  S.N_anti.antitoneOn ha (mem_Ici.2 (le_trans ha hat)) hat

theorem x_ne_of_zero {a : ℝ} (ha : a ∈ Ici s0) (hya : V a = 2) : U a - 1 ≠ 0 := by
  intro h
  have := S.N_pos ha
  rw [h, hya] at this; unfold Nw at this; norm_num at this

/-- At the left end of a segment on the side `σ`, `σ x > 0`. -/
theorem side_left {a b σ : ℝ} (ha : a ∈ Ici s0) (hab : a < b) (hya : V a = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : 0 < σ * (U a - 1) := by
  have ap := S.tpos ha
  have hd : HasDerivAt (fun t => σ * (V t - 2)) (σ * (V a * (U a - 1) / a)) a :=
    ((S.hV a ha).sub_const 2).const_mul σ
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | heq
  · have hneg : σ * (V a * (U a - 1) / a) < 0 := by
      rw [hya]
      have : σ * (2 * (U a - 1) / a) = 2 * (σ * (U a - 1)) / a := by ring
      rw [this]; exact div_neg_of_neg_of_pos (by linarith) ap
    have ev := Checked.Math.GelfandExtremaMain.right_lt hd hneg
    have ev2 : ∀ᶠ t in 𝓝[>] a, t ∈ Ioo a b := Ioo_mem_nhdsGT hab
    obtain ⟨t, h1, h2⟩ := (ev.and ev2).exists
    have := hsg t h2
    simp only [hya, sub_self, mul_zero] at h1
    linarith
  · have hσ0 : σ ≠ 0 := by
      intro h0; obtain ⟨t, ht⟩ := nonempty_Ioo.2 hab; have := hsg t ht; rw [h0] at this; simp at this
    have := x_ne_of_zero S ha hya
    exact this (by rcases mul_eq_zero.1 heq with h | h; exact absurd h hσ0; exact h)

/-- At the right end of a segment on the side `σ`, `σ x < 0`. -/
theorem side_right {a b σ : ℝ} (ha : a ∈ Ici s0) (hab : a < b) (hyb : V b = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : σ * (U b - 1) < 0 := by
  have hb : b ∈ Ici s0 := mem_Ici.2 (le_trans ha hab.le)
  have bp := S.tpos hb
  have hd : HasDerivAt (fun t => σ * (V t - 2)) (σ * (V b * (U b - 1) / b)) b :=
    ((S.hV b hb).sub_const 2).const_mul σ
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | heq
  · have hpos : 0 < σ * (V b * (U b - 1) / b) := by
      rw [hyb]
      have : σ * (2 * (U b - 1) / b) = 2 * (σ * (U b - 1)) / b := by ring
      rw [this]; exact div_pos (by linarith) bp
    have ev := Checked.Math.GelfandExtremaMain.left_lt hd hpos
    have ev2 : ∀ᶠ t in 𝓝[<] b, t ∈ Ioo a b := Ioo_mem_nhdsLT hab
    obtain ⟨t, h1, h2⟩ := (ev.and ev2).exists
    have := hsg t h2
    simp only [hyb, sub_self, mul_zero] at h1
    linarith
  · have hσ0 : σ ≠ 0 := by
      intro h0; obtain ⟨t, ht⟩ := nonempty_Ioo.2 hab; have := hsg t ht; rw [h0] at this; simp at this
    have := x_ne_of_zero S hb hyb
    exact this (by rcases mul_eq_zero.1 heq.symm with h | h; exact absurd h hσ0; exact h)

theorem th_left {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hya : V a = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : th σ U V a = 0 := by
  unfold th fc
  have h := fc_at_zero hσ (side_left S ha hab hya hsg)
  rw [hya, sub_self] at *
  rw [h, Real.arccos_one]

theorem th_right {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hyb : V b = 2)
    (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) : th σ U V b = Real.pi := by
  unfold th fc
  have h := fc_at_zero' hσ (side_right S ha hab hyb hsg)
  rw [hyb, sub_self] at *
  rw [h, Real.arccos_neg_one]

end Sys
end GTR
namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus

theorem six_sqrt7 : 6 * Real.sqrt 7 ≤ 16 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  nlinarith [Real.sqrt_nonneg 7]

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem sqrtN_le {a t : ℝ} (ha : a ∈ Ici s0) (hat : a ≤ t) :
    Real.sqrt (Nw (U t - 1) (V t - 2)) ≤ Real.sqrt (Nw (U a - 1) (V a - 2)) :=
  Real.sqrt_le_sqrt (N_le_of S ha hat)

theorem logN_deriv {t : ℝ} (ht : t ∈ Ici s0) :
    HasDerivAt (fun t => Real.log (Nw (U t - 1) (V t - 2)))
      (Dq (U t - 1) (V t - 2) / t / Nw (U t - 1) (V t - 2)) t :=
  (S.dN ht).log (S.N_pos ht).ne'

theorem logN_cont {a b : ℝ} (ha : a ∈ Ici s0) :
    ContinuousOn (fun t => Real.log (Nw (U t - 1) (V t - 2))) (Icc a b) := by
  intro t ht
  have ht' : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1)
  exact (logN_deriv S ht').continuousAt.continuousWithinAt

theorem log_cont {a b : ℝ} (ha : a ∈ Ici s0) : ContinuousOn Real.log (Icc a b) := by
  intro t ht
  have ht' : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1)
  exact (Real.continuousAt_log (S.tpos ht').ne').continuousWithinAt

/-- Bounds on one segment between consecutive zeros of `y`: the angle advances by pi, which bounds the
advance of log t, and log Nw advances at rate −1 up to `36 √Nw`. -/
theorem seg_bounds {a b σ : ℝ} (hσ : σ ^ 2 = 1) (ha : a ∈ Ici s0) (hab : a < b) (hya : V a = 2)
    (hyb : V b = 2) (hsg : ∀ t ∈ Ioo a b, 0 < σ * (V t - 2)) :
    (Real.sqrt 7 / 2 - 16 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ≤ Real.pi ∧
    Real.pi ≤ (Real.sqrt 7 / 2 + 16 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ∧
    -(1 + 36 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) ≤
      Real.log (Nw (U b - 1) (V b - 2)) - Real.log (Nw (U a - 1) (V a - 2)) ∧
    Real.log (Nw (U b - 1) (V b - 2)) - Real.log (Nw (U a - 1) (V a - 2)) ≤
      -(1 - 36 * Real.sqrt (Nw (U a - 1) (V a - 2))) * (Real.log b - Real.log a) := by
  set ε := Real.sqrt (Nw (U a - 1) (V a - 2)) with hε
  have hIcc : ∀ t ∈ Icc a b, t ∈ Ici s0 := fun t ht => mem_Ici.2 (le_trans ha ht.1)
  have hIoo : ∀ t ∈ Ioo a b, t ∈ Ici s0 := fun t ht => hIcc t (Ioo_subset_Icc_self ht)
  have th_c : ContinuousOn (th σ U V) (Icc a b) := (th_cont S).mono (fun t ht => hIcc t ht)
  have lc := log_cont S (b := b) ha
  have lN := logN_cont S (b := b) ha
  have tha := th_left S hσ ha hab hya hsg
  have thb := th_right S hσ ha hab hyb hsg
  have s7 := six_sqrt7
  -- pointwise facts inside
  have inside : ∀ t ∈ Ioo a b, 0 < t ∧ 0 < Nw (U t - 1) (V t - 2) ∧
      Real.sqrt (Nw (U t - 1) (V t - 2)) ≤ ε ∧
      |Lq (U t - 1) (V t - 2) - Nw (U t - 1) (V t - 2) / 4| ≤
        3 * Nw (U t - 1) (V t - 2) * Real.sqrt (Nw (U t - 1) (V t - 2)) ∧
      |Dq (U t - 1) (V t - 2) + Nw (U t - 1) (V t - 2)| ≤
        36 * Nw (U t - 1) (V t - 2) * Real.sqrt (Nw (U t - 1) (V t - 2)) := fun t ht =>
    ⟨S.tpos (hIoo t ht), S.N_pos (hIoo t ht), sqrtN_le S ha ht.1.le, Lq_err _ _, Dq_err _ _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := le_of_deriv (G := fun t => th σ U V t - (Real.sqrt 7 / 2 - 16 * ε) * Real.log t)
      (G' := fun t => 2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t) -
        (Real.sqrt 7 / 2 - 16 * ε) * t⁻¹) hab.le (th_c.sub (continuousOn_const.mul lc))
      (fun t ht => (th_deriv S hσ (hIoo t ht) (hsg t ht)).sub
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
  · have := le_of_deriv (G := fun t => (Real.sqrt 7 / 2 + 16 * ε) * Real.log t - th σ U V t)
      (G' := fun t => (Real.sqrt 7 / 2 + 16 * ε) * t⁻¹ -
        2 * Real.sqrt 7 * Lq (U t - 1) (V t - 2) / (Nw (U t - 1) (V t - 2) * t)) hab.le
      ((continuousOn_const.mul lc).sub th_c)
      (fun t ht => ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _).sub
        (th_deriv S hσ (hIoo t ht) (hsg t ht)))
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
      (fun t ht => (logN_deriv S (hIoo t ht)).add ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
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
      (fun t ht => (logN_deriv S (hIoo t ht)).neg.sub ((Real.hasDerivAt_log (inside t ht).1.ne').const_mul _))
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
end GTR
