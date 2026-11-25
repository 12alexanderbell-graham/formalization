import Checked.Math.BEFocus
import Checked.Math.GelfandExtremaMain
import Checked.Math.BEAllMain
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
namespace GTR
open Set Filter Topology

/-- The squeeze: per-segment bounds with errors tending to zero give the limit of the log-advance. -/
theorem lim_D {ε L D : ℕ → ℝ} {K : ℕ} (hε : Tendsto ε atTop (𝓝 0))
    (h1 : ∀ k, K ≤ k → (Real.sqrt 7 / 2 - 16 * ε k) * L k ≤ Real.pi)
    (h2 : ∀ k, K ≤ k → Real.pi ≤ (Real.sqrt 7 / 2 + 16 * ε k) * L k)
    (h3 : ∀ k, K ≤ k → -(1 + 36 * ε k) * L k ≤ D k)
    (h4 : ∀ k, K ≤ k → D k ≤ -(1 - 36 * ε k) * L k) :
    Tendsto D atTop (𝓝 (-(Real.pi / (Real.sqrt 7 / 2)))) := by
  set c := Real.sqrt 7 / 2 with hc
  have cpos : 0 < c := by positivity
  -- eventually the error is small
  have hsmall : ∀ᶠ k in atTop, K ≤ k ∧ 16 * ε k < c / 2 ∧ 36 * ε k < 1 / 2 ∧ -(c / 32) < ε k := by
    have e1 : ∀ᶠ k in atTop, 16 * ε k < c / 2 := by
      have : Tendsto (fun k => 16 * ε k) atTop (𝓝 (16 * 0)) := hε.const_mul 16
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    have e2 : ∀ᶠ k in atTop, 36 * ε k < 1 / 2 := by
      have : Tendsto (fun k => 36 * ε k) atTop (𝓝 (36 * 0)) := hε.const_mul 36
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    have e3 : ∀ᶠ k in atTop, -(c / 32) < ε k := hε.eventually (lt_mem_nhds (by linarith))
    filter_upwards [eventually_ge_atTop K, e1, e2, e3] with k a b c' d using ⟨a, b, c', d⟩
  -- L between pi/(c + 16ε) and pi/(c - 16ε)
  have hLlo : Tendsto (fun k => Real.pi / (c + 16 * ε k)) atTop (𝓝 (Real.pi / c)) := by
    have : Tendsto (fun k => c + 16 * ε k) atTop (𝓝 (c + 16 * 0)) := (hε.const_mul 16).const_add c
    rw [mul_zero, add_zero] at this
    exact tendsto_const_nhds.div this cpos.ne'
  have hLhi : Tendsto (fun k => Real.pi / (c - 16 * ε k)) atTop (𝓝 (Real.pi / c)) := by
    have : Tendsto (fun k => c - 16 * ε k) atTop (𝓝 (c - 16 * 0)) := (hε.const_mul 16).const_sub c
    rw [mul_zero, sub_zero] at this
    exact tendsto_const_nhds.div this cpos.ne'
  have hL : Tendsto L atTop (𝓝 (Real.pi / c)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLlo hLhi ?_ ?_
    · filter_upwards [hsmall] with k hk'
      obtain ⟨hk, a, -, a3⟩ := hk'
      have hp : 0 < c + 16 * ε k := by linarith
      rw [div_le_iff₀ hp]; linarith [h2 k hk]
    · filter_upwards [hsmall] with k hk'
      obtain ⟨hk, a, -, a3⟩ := hk'
      have hp : 0 < c - 16 * ε k := by linarith
      rw [le_div_iff₀ hp]; linarith [h1 k hk]
  have hlo : Tendsto (fun k => -(1 + 36 * ε k) * L k) atTop (𝓝 (-(1 + 36 * 0) * (Real.pi / c))) :=
    (((hε.const_mul 36).const_add 1).neg).mul hL
  have hhi : Tendsto (fun k => -(1 - 36 * ε k) * L k) atTop (𝓝 (-(1 - 36 * 0) * (Real.pi / c))) :=
    (((hε.const_mul 36).const_sub 1).neg).mul hL
  norm_num at hlo hhi
  have e : -(Real.pi / c) = -(Real.pi / c) := rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun k => -(1 + 36 * ε k) * L k)
    (h := fun k => -(1 - 36 * ε k) * L k) ?_ ?_ ?_ ?_
  · simpa using hlo
  · simpa using hhi
  · filter_upwards [hsmall] with k hk' using h3 k hk'.1
  · filter_upwards [hsmall] with k hk' using h4 k hk'.1

theorem lim_q {D q : ℕ → ℝ} {K : ℕ}
    (hD : Tendsto D atTop (𝓝 (-(Real.pi / (Real.sqrt 7 / 2)))))
    (hq : ∀ k, K ≤ k → q k = -Real.exp (D k / 2)) :
    Tendsto q atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) := by
  have h : Tendsto (fun k => -Real.exp (D k / 2)) atTop
      (𝓝 (-Real.exp (-(Real.pi / (Real.sqrt 7 / 2)) / 2))) :=
    ((Real.continuous_exp.tendsto _).comp (hD.div_const 2)).neg
  have e : -(Real.pi / (Real.sqrt 7 / 2)) / 2 = -(Real.pi / Real.sqrt 7) := by
    have : Real.sqrt 7 ≠ 0 := by positivity
    field_simp
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop K] with k hk using (hq k hk).symm

end GTR
namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (lam U V Hyp hyp_of U_deriv V_deriv lam_deriv lam_eq_UV phi_neg
  right_gt right_lt left_lt left_gt)

section
variable {w φ : ℝ → ℝ} (E : Hyp w φ) {s0 : ℝ} (S : Sys (U w φ) (V φ) s0)
include E S

omit E in
/-- Inside a segment where λ keeps one sign of slope, `V − 2` cannot vanish (transversality). -/
theorem no_zero_inside {a b σ t : ℝ} (ha : a ∈ Ici s0) (ht : t ∈ Ioo a b)
    (hnn : ∀ t ∈ Ioo a b, 0 ≤ σ * (V φ t - 2)) (hσ : σ ^ 2 = 1) : V φ t ≠ 2 := by
  intro hV
  have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
  have tp := S.tpos ht0
  have hx := GTR.Sys.x_ne_of_zero S ht0 hV
  have hd : HasDerivAt (fun s => σ * (V φ s - 2)) (σ * (V φ t * (U w φ t - 1) / t)) t :=
    ((S.hV t ht0).sub_const 2).const_mul σ
  have hσ0 : σ ≠ 0 := by rintro h; rw [h] at hσ; norm_num at hσ
  have hd0 : σ * (V φ t * (U w φ t - 1) / t) ≠ 0 := by
    rw [hV]; exact mul_ne_zero hσ0 (div_ne_zero (mul_ne_zero two_ne_zero hx) tp.ne')
  have hval : σ * (V φ t - 2) = 0 := by rw [hV]; ring
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · obtain ⟨s, h1, h2⟩ := ((right_lt hd hneg).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hnn s ⟨ht.1.trans h2.1, h2.2⟩
    simp only [hval] at h1; linarith
  · obtain ⟨s, h1, h2⟩ := ((left_lt hd hpos).and (Ioo_mem_nhdsLT ht.1)).exists
    have := hnn s ⟨h2.1, h2.2.trans ht.2⟩
    simp only [hval] at h1; linarith

/-- On a segment where λ decreases, `V > 2` inside. -/
theorem pos_of_anti {a b : ℝ} (ha : a ∈ Ici s0) (hanti : StrictAntiOn (lam w) (Icc a b)) :
    ∀ t ∈ Ioo a b, 0 < (1 : ℝ) * (V φ t - 2) := by
  have hnn : ∀ t ∈ Ioo a b, 0 ≤ (1 : ℝ) * (V φ t - 2) := by
    intro t ht
    have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
    have tp := S.tpos ht0
    by_contra hc
    push Not at hc
    have hd := lam_deriv E tp
    have hpos : 0 < t * Real.exp (w t) * (2 + t * φ t) := by
      have : 2 + t * φ t = -(V φ t - 2) := by unfold V; ring
      rw [this]; apply mul_pos (by positivity); linarith
    obtain ⟨s, h1, h2⟩ := ((right_gt hd hpos).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hanti ⟨ht.1.le, ht.2.le⟩ ⟨(ht.1.trans h2.1).le, h2.2.le⟩ h2.1
    linarith
  intro t ht
  rcases (hnn t ht).lt_or_eq with h | h
  · exact h
  · exact absurd (by linarith : V φ t = 2) (no_zero_inside S ha ht hnn (by norm_num))

/-- On a segment where λ increases, `V < 2` inside. -/
theorem neg_of_mono {a b : ℝ} (ha : a ∈ Ici s0) (hmono : StrictMonoOn (lam w) (Icc a b)) :
    ∀ t ∈ Ioo a b, 0 < (-1 : ℝ) * (V φ t - 2) := by
  have hnn : ∀ t ∈ Ioo a b, 0 ≤ (-1 : ℝ) * (V φ t - 2) := by
    intro t ht
    have ht0 : t ∈ Ici s0 := mem_Ici.2 (le_trans ha ht.1.le)
    have tp := S.tpos ht0
    by_contra hc
    push Not at hc
    have hd := lam_deriv E tp
    have hneg : t * Real.exp (w t) * (2 + t * φ t) < 0 := by
      have : 2 + t * φ t = -(V φ t - 2) := by unfold V; ring
      rw [this]; apply mul_neg_of_pos_of_neg (by positivity); linarith
    obtain ⟨s, h1, h2⟩ := ((right_lt hd hneg).and (Ioo_mem_nhdsGT ht.2)).exists
    have := hmono ⟨ht.1.le, ht.2.le⟩ ⟨(ht.1.trans h2.1).le, h2.2.le⟩ h2.1
    linarith
  intro t ht
  rcases (hnn t ht).lt_or_eq with h | h
  · exact h
  · exact absurd (by linarith : V φ t = 2) (no_zero_inside S ha ht hnn (by norm_num))

end

/-- At a local extremum of λ at a positive radius, `V = 2`. -/
theorem V_two_of_extr {w φ : ℝ → ℝ} (E : Hyp w φ) {z : ℝ} (hz : 0 < z)
    (h : IsLocalMin (lam w) z ∨ IsLocalMax (lam w) z) : V φ z = 2 := by
  have hd := lam_deriv E hz
  have h0 : z * Real.exp (w z) * (2 + z * φ z) = 0 := by
    rcases h with h | h
    · exact h.hasDerivAt_eq_zero hd
    · exact h.hasDerivAt_eq_zero hd
  have : 2 + z * φ z = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  unfold V; linarith

theorem q_eq {xa xb Na Nb : ℝ} (hNa : Na = 8 * xa ^ 2) (hNb : Nb = 8 * xb ^ 2) (hs : xb * xa < 0) :
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

end GTR
namespace GTR
open Set Filter Topology
open Checked.Math.BEOCell (Nw)
open Checked.Math.BEFocus
open Checked.Math.GelfandExtremaMain (lam U V Hyp hyp_of U_deriv V_deriv lam_deriv lam_eq_UV phi_neg)

theorem ratio_main (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      4.071496844 ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      3.321992118 ≤ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ∧ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ≤ 3.321992119 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ζ 0 → s ^ 2 * Real.exp (w s) < ζ 0 ^ 2 * Real.exp (w (ζ 0))) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k)), s ≠ ζ (2 * k + 1) →
        ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < s ^ 2 * Real.exp (w s)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k + 1)), s ≠ ζ (2 * k + 2) →
        s ^ 2 * Real.exp (w s) < ζ (2 * k + 2) ^ 2 * Real.exp (w (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < 2 ∧
        2 < ζ (2 * k) ^ 2 * Real.exp (w (ζ (2 * k)))) ∧
      Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 2) ∧
      StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ,
        StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      Tendsto (fun k : ℕ => (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) /
        (ζ k ^ 2 * Real.exp (w (ζ k)) - 2)) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) := by
  obtain ⟨ζ, hm, hT, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono⟩ :=
    Checked.Math.GelfandExtremaMain.main w φ hw hφ0 hφ h0
  refine ⟨ζ, hm, hT, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, ?_⟩
  have E := hyp_of hw hφ0 hφ
  obtain ⟨r1, r2, r3⟩ := Checked.Math.BEAllMain.restrict 300000 hw hφ0 hφ
  obtain ⟨-, su, sv, -⟩ := Checked.Math.BEState300.state300 300000 le_rfl w φ r1 r2 r3 h0
  obtain ⟨N0le, N0pos⟩ := Checked.Math.BEAllMain.N0_bounds su sv
  have S : Sys (U w φ) (V φ) 300000 :=
    ⟨by norm_num, fun t ht => U_deriv E (by linarith [mem_Ici.1 ht]),
      fun t ht => V_deriv E (by linarith [mem_Ici.1 ht]), le_trans N0le (by norm_num), N0pos⟩
  have ζpos : ∀ n, 0 < ζ n := fun n =>
    lt_of_lt_of_le (by norm_num at hz0lo; linarith) (hm.monotone (Nat.zero_le n))
  -- the turning points are zeros of V − 2
  have hVz : ∀ n, V φ (ζ n) = 2 := by
    intro n
    apply V_two_of_extr E (ζpos n)
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases m with _ | j
      · right
        filter_upwards [Ici_mem_nhds (ζpos 0)] with s hs
        by_cases h : s = ζ 0
        · rw [h]
        · exact (hmax0 s hs h).le
      · right
        have e : 2 * (j + 1) = 2 * j + 2 := by ring
        rw [e]
        filter_upwards [Ici_mem_nhds (hm (show 2 * j + 1 < 2 * j + 2 by omega))] with s hs
        by_cases h : s = ζ (2 * j + 2)
        · rw [h]
        · exact (hmax j s hs h).le
    · left
      filter_upwards [Ici_mem_nhds (hm (show 2 * m < 2 * m + 1 by omega))] with s hs
      by_cases h : s = ζ (2 * m + 1)
      · rw [h]
      · exact (hmin m s hs h).le
  -- from some index on, the turning points lie beyond 300000
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hT.eventually (eventually_ge_atTop (300000 : ℝ)))
  have hKi : ∀ k, K ≤ k → ζ k ∈ Ici (300000 : ℝ) := fun k hk => mem_Ici.2 (hK k hk)
  -- the side of each segment
  have side : ∀ k, K ≤ k → ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ t ∈ Ioo (ζ k) (ζ (k + 1)), 0 < σ * (V φ t - 2) := by
    intro k hk
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · exact ⟨1, by norm_num, pos_of_anti E S (hKi _ hk) (hanti m)⟩
    · exact ⟨-1, by norm_num, neg_of_mono E S (hKi _ hk) (hmono m)⟩
  have B : ∀ k, K ≤ k →
      (Real.sqrt 7 / 2 - 16 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
        (Real.log (ζ (k + 1)) - Real.log (ζ k)) ≤ Real.pi ∧
      Real.pi ≤ (Real.sqrt 7 / 2 + 16 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
        (Real.log (ζ (k + 1)) - Real.log (ζ k)) ∧
      -(1 + 36 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
          (Real.log (ζ (k + 1)) - Real.log (ζ k)) ≤
        Real.log (Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2)) -
          Real.log (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) ∧
      Real.log (Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2)) -
          Real.log (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) ≤
        -(1 - 36 * Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2))) *
          (Real.log (ζ (k + 1)) - Real.log (ζ k)) := fun k hk => by
    obtain ⟨σ, hσ, hsg⟩ := side k hk
    exact GTR.Sys.seg_bounds S hσ (hKi k hk) (hm (Nat.lt_succ_self k)) (hVz k) (hVz (k + 1)) hsg
  set ε : ℕ → ℝ := fun k => Real.sqrt (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) with hεdef
  set L : ℕ → ℝ := fun k => Real.log (ζ (k + 1)) - Real.log (ζ k) with hLdef
  set D : ℕ → ℝ := fun k => Real.log (Nw (U w φ (ζ (k + 1)) - 1) (V φ (ζ (k + 1)) - 2)) -
    Real.log (Nw (U w φ (ζ k) - 1) (V φ (ζ k) - 2)) with hDdef
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (S.N_tendsto.comp hT)
    rw [Real.sqrt_zero] at this
    exact this
  have hD := lim_D (ε := ε) (L := L) (D := D) (K := K) hε (fun k hk => (B k hk).1)
    (fun k hk => (B k hk).2.1) (fun k hk => (B k hk).2.2.1) (fun k hk => (B k hk).2.2.2)
  -- the quotient at the turning points
  have lam2 : ∀ n, ζ n ^ 2 * Real.exp (w (ζ n)) - 2 = 2 * (U w φ (ζ n) - 1) := by
    intro n
    have := lam_eq_UV E (ζpos n)
    unfold lam at this
    rw [this, hVz n]; ring
  have Nz : ∀ n, Nw (U w φ (ζ n) - 1) (V φ (ζ n) - 2) = 8 * (U w φ (ζ n) - 1) ^ 2 := by
    intro n; rw [hVz n]; unfold Nw; ring
  have alt : ∀ n, (ζ (n + 1) ^ 2 * Real.exp (w (ζ (n + 1))) - 2) *
      (ζ n ^ 2 * Real.exp (w (ζ n)) - 2) < 0 := by
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
  apply lim_q hD (K := K)
  intro k _
  rw [lam2 (k + 1), lam2 k]
  have hs : (U w φ (ζ (k + 1)) - 1) * (U w φ (ζ k) - 1) < 0 := by
    have := alt k; rw [lam2 (k + 1), lam2 k] at this; nlinarith
  rw [show 2 * (U w φ (ζ (k + 1)) - 1) / (2 * (U w φ (ζ k) - 1)) =
    (U w φ (ζ (k + 1)) - 1) / (U w φ (ζ k) - 1) by
      rw [mul_div_mul_left _ _ two_ne_zero]]
  exact q_eq (Nz k) (Nz (k + 1)) hs

end GTR
#print axioms GTR.ratio_main
