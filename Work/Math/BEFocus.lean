import Mathlib
import Checked.Math.BEOCell

/-! Bonnor–Ebert sphere, `BEFocus`: the homology system u' = u(3 − u − v)/t, v' = v(u − 1)/t near its focus
(1, 2), with no certificates. In the weighted norm `Checked.Math.BEOCell.Nw` of the focus' real Jordan basis the
ball `Nw (u − 1) (v − 2) ≤ 1/400` is forward invariant and `Nw` decreases; the angular momentum about the focus
is positive, so 2u − v changes sign infinitely often, each zero transversal (derivative 8u(1 − u)/t); at the
zeros `Nw = 32 (u − 1)²`. Written for `BonnorEbertAll` (run 2026-11-15T0028Z). -/

namespace Work.Math.BEFocus
open Set Filter Topology
open Checked.Math.BEOCell (Nw)

/-! ### Algebra in the focus coordinates x = u − 1, y = v − 2 -/

/-- The derivative of `Nw` along the field (times t). -/
def Dq (x y : ℝ) : ℝ := -Nw x y - 4 * x * (4 * x ^ 2 + 4 * x * y - y ^ 2)

/-- The angular momentum about the focus (times t). -/
def Lq (x y : ℝ) : ℝ := x * ((2 + y) * x) - y * ((1 + x) * (-x - y))

theorem ball {x y : ℝ} (h : Nw x y ≤ 1 / 400) : |x| ≤ 1 / 50 ∧ |y| ≤ 7 / 200 := by
  have := Checked.Math.BEOCell.coords (e1 := x) (e2 := y) (r := 1 / 20) (by norm_num)
    (by norm_num; linarith)
  constructor
  · linarith [this.1]
  · linarith [this.2]

theorem Dq_upper {x y : ℝ} (h : Nw x y ≤ 1 / 400) : Dq x y ≤ -(Nw x y / 2) := by
  obtain ⟨hx, -⟩ := ball h
  have hx1 := abs_le.1 hx
  have p1 : 0 ≤ 54 * x ^ 2 + 29 * x * y + 24 * y ^ 2 := by nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
  have p2 : 0 ≤ 46 * x ^ 2 + 21 * x * y + 26 * y ^ 2 := by nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
  unfold Dq Nw at *
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 50 + x) p1,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 50 - x) p2]

theorem Dq_lower {x y : ℝ} (h : Nw x y ≤ 1 / 400) : -(3 / 2 * Nw x y) ≤ Dq x y := by
  obtain ⟨hx, -⟩ := ball h
  have hx1 := abs_le.1 hx
  have p1 : 0 ≤ 54 * x ^ 2 + 29 * x * y + 24 * y ^ 2 := by nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
  have p2 : 0 ≤ 46 * x ^ 2 + 21 * x * y + 26 * y ^ 2 := by nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]
  unfold Dq Nw at *
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 50 + x) p2,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 50 - x) p1]

theorem Lq_lower {x y : ℝ} (h : Nw x y ≤ 1 / 400) : (x ^ 2 + y ^ 2) / 2 ≤ Lq x y := by
  obtain ⟨hx, hy⟩ := ball h
  have hx1 := abs_le.1 hx
  have hy1 := abs_le.1 hy
  have q1 : 0 ≤ 3 / 2 * x ^ 2 + x * y + 1 / 2 * y ^ 2 + 3 / 40 * (x * y) := by
    nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y, sq_nonneg (2 * x + y)]
  have q2 : 0 ≤ 3 / 2 * x ^ 2 + x * y + 1 / 2 * y ^ 2 - 3 / 40 * (x * y) := by
    nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y, sq_nonneg (2 * x + y)]
  have e : Lq x y - (x ^ 2 + y ^ 2) / 2 = 3 / 2 * x ^ 2 + x * y + 1 / 2 * y ^ 2 + (2 * x + y) * (x * y) := by
    unfold Lq; ring
  have c1 : 0 ≤ 3 / 40 + (2 * x + y) := by linarith
  have c2 : 0 ≤ 3 / 40 - (2 * x + y) := by linarith
  nlinarith [mul_nonneg c1 q1, mul_nonneg c2 q2]

theorem Nw_pos_of_ne {x y : ℝ} (h : 0 < Nw x y) : x ≠ 0 ∨ y ≠ 0 := by
  by_contra hc; push Not at hc; rw [hc.1, hc.2] at h; unfold Nw at h; norm_num at h

theorem g_sq_le (x y : ℝ) : (2 * x - y) ^ 2 ≤ 5 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x + 2 * y)]

theorem x_sq_le_Nw (x y : ℝ) : x ^ 2 ≤ Nw x y := by unfold Nw; nlinarith [sq_nonneg (x + 2 * y)]

theorem y_abs_le (x y : ℝ) : |y| ≤ Real.sqrt (Nw x y) := by
  have hN : 0 ≤ Nw x y := Checked.Math.BEOCell.Nw_nonneg x y
  have h1 : |x| ≤ Real.sqrt (Nw x y) := Real.abs_le_sqrt (x_sq_le_Nw x y)
  have h2 : |x + 2 * y| ≤ Real.sqrt (Nw x y) := Real.abs_le_sqrt (by unfold Nw; nlinarith [sq_nonneg x])
  have : |2 * y| ≤ |x + 2 * y| + |x| := by
    calc |2 * y| = |(x + 2 * y) - x| := by ring_nf
      _ ≤ |x + 2 * y| + |x| := abs_sub _ _
  rw [abs_mul, abs_two] at this
  have := Real.sqrt_nonneg (Nw x y)
  linarith

/-! ### Derivatives along a solution -/

section
variable {U V : ℝ → ℝ} {t : ℝ}

theorem hasDerivAt_N {u' v' : ℝ} (hu : HasDerivAt U u' t) (hv : HasDerivAt V v' t) :
    HasDerivAt (fun t => Nw (U t - 1) (V t - 2))
      (14 * (U t - 1) * u' + 2 * ((U t - 1) + 2 * (V t - 2)) * (u' + 2 * v')) t := by
  have h := (((hu.sub_const 1).pow 2).const_mul 7).add
    (((hu.sub_const 1).add ((hv.sub_const 2).const_mul 2)).pow 2)
  unfold Nw
  convert h using 1
  simp only [Pi.add_apply]; push_cast; ring

theorem N_deriv_eq (ht : t ≠ 0) :
    14 * (U t - 1) * (U t * (3 - U t - V t) / t) +
      2 * ((U t - 1) + 2 * (V t - 2)) * (U t * (3 - U t - V t) / t + 2 * (V t * (U t - 1) / t)) =
      Dq (U t - 1) (V t - 2) / t := by
  unfold Dq Nw; field_simp; ring

end

/-! ### Monotonicity helpers -/

theorem monoOn_Ici {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Ioi a, 0 ≤ f' t) : MonotoneOn f (Ici a) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici a)
  · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
  · rw [interior_Ici]; exact fun t ht => (hf t (mem_Ici.2 (le_of_lt ht))).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro t ht; rw [(hf t (mem_Ici.2 (le_of_lt ht))).deriv]; exact h t ht

theorem antiOn_Ici {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Ioi a, f' t ≤ 0) : AntitoneOn f (Ici a) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici a)
  · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
  · rw [interior_Ici]; exact fun t ht => (hf t (mem_Ici.2 (le_of_lt ht))).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro t ht; rw [(hf t (mem_Ici.2 (le_of_lt ht))).deriv]; exact h t ht

theorem sAntiOn_Ici {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Ioi a, f' t < 0) : StrictAntiOn f (Ici a) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici a)
  · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
  · rw [interior_Ici]; intro t ht; rw [(hf t (mem_Ici.2 (le_of_lt ht))).deriv]; exact h t ht

theorem monoOn_Icc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Ioo a b, 0 ≤ f' t) : MonotoneOn f (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
  · rw [interior_Icc]; exact fun t ht => (hf t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro t ht; rw [(hf t (Ioo_subset_Icc_self ht)).deriv]; exact h t ht

/-! ### The system near the focus -/

/-- Hypotheses on a solution of the homology system from `s0` on, starting in the ball. -/
structure Sys (U V : ℝ → ℝ) (s0 : ℝ) : Prop where
  pos : 0 < s0
  hU : ∀ t ∈ Ici s0, HasDerivAt U (U t * (3 - U t - V t) / t) t
  hV : ∀ t ∈ Ici s0, HasDerivAt V (V t * (U t - 1) / t) t
  hN0 : Nw (U s0 - 1) (V s0 - 2) ≤ 1 / 400
  hNpos : 0 < Nw (U s0 - 1) (V s0 - 2)

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem tpos {t : ℝ} (ht : t ∈ Ici s0) : 0 < t := lt_of_lt_of_le S.pos ht

theorem dN {t : ℝ} (ht : t ∈ Ici s0) :
    HasDerivAt (fun t => Nw (U t - 1) (V t - 2)) (Dq (U t - 1) (V t - 2) / t) t := by
  have h := hasDerivAt_N (S.hU t ht) (S.hV t ht)
  rwa [N_deriv_eq (S.tpos ht).ne'] at h

theorem contN : ContinuousOn (fun t => Nw (U t - 1) (V t - 2)) (Ici s0) :=
  fun t ht => (S.dN ht).continuousAt.continuousWithinAt

/-- The ball is forward invariant: `Nw` never exceeds its start value. -/
theorem N_le {t : ℝ} (ht : t ∈ Ici s0) : Nw (U t - 1) (V t - 2) ≤ Nw (U s0 - 1) (V s0 - 2) := by
  have := image_le_of_deriv_right_lt_deriv_boundary' (a := s0) (b := t)
    (f := fun t => Nw (U t - 1) (V t - 2)) (f' := fun t => Dq (U t - 1) (V t - 2) / t)
    (B := fun _ => Nw (U s0 - 1) (V s0 - 2)) (B' := fun _ => 0)
    (S.contN.mono Icc_subset_Ici_self)
    (fun x hx => (S.dN hx.1).hasDerivWithinAt) le_rfl continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hfx => by
      have hxp := S.tpos hx.1
      have hfx' : Nw (U x - 1) (V x - 2) = Nw (U s0 - 1) (V s0 - 2) := hfx
      have hb : Nw (U x - 1) (V x - 2) ≤ 1 / 400 := by rw [hfx']; exact S.hN0
      have := Dq_upper hb
      show Dq (U x - 1) (V x - 2) / x < 0
      rw [div_lt_iff₀ hxp]
      rw [hfx'] at this
      nlinarith [S.hNpos])
  exact this ⟨ht, le_rfl⟩

theorem N_ball {t : ℝ} (ht : t ∈ Ici s0) : Nw (U t - 1) (V t - 2) ≤ 1 / 400 :=
  (S.N_le ht).trans S.hN0

/-- `Nw` stays positive: N² t³ is nondecreasing. -/
theorem N_pos {t : ℝ} (ht : t ∈ Ici s0) : 0 < Nw (U t - 1) (V t - 2) := by
  have hm : MonotoneOn (fun t => Nw (U t - 1) (V t - 2) ^ 2 * t ^ 3) (Ici s0) := by
    apply monoOn_Ici (f' := fun t => 2 * Nw (U t - 1) (V t - 2) * (Dq (U t - 1) (V t - 2) / t) * t ^ 3
      + Nw (U t - 1) (V t - 2) ^ 2 * (3 * t ^ 2))
    · intro t ht
      have h := ((S.dN ht).pow 2).mul (hasDerivAt_pow 3 t)
      exact h.congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)
    · intro t ht
      have htp := S.tpos (mem_Ici.2 (le_of_lt ht))
      have hb := S.N_ball (mem_Ici.2 (le_of_lt ht))
      have hl := Dq_lower hb
      have hN := Checked.Math.BEOCell.Nw_nonneg (U t - 1) (V t - 2)
      have e : 2 * Nw (U t - 1) (V t - 2) * (Dq (U t - 1) (V t - 2) / t) * t ^ 3
          + Nw (U t - 1) (V t - 2) ^ 2 * (3 * t ^ 2) =
          Nw (U t - 1) (V t - 2) * t ^ 2 * (2 * Dq (U t - 1) (V t - 2) + 3 * Nw (U t - 1) (V t - 2)) := by
        field_simp; try ring
      rw [e]
      apply mul_nonneg (mul_nonneg hN (by positivity)); linarith
  have h := hm (mem_Ici.2 le_rfl) ht ht
  have h1 : 0 < Nw (U s0 - 1) (V s0 - 2) ^ 2 * s0 ^ 3 := by have := S.pos; have := S.hNpos; positivity
  simp only at h
  have h2 : 0 < Nw (U t - 1) (V t - 2) ^ 2 * t ^ 3 := lt_of_lt_of_le h1 h
  rcases (Checked.Math.BEOCell.Nw_nonneg (U t - 1) (V t - 2)).lt_or_eq with h3 | h3
  · exact h3
  · rw [← h3] at h2; simp at h2

theorem N_anti : StrictAntiOn (fun t => Nw (U t - 1) (V t - 2)) (Ici s0) := by
  apply sAntiOn_Ici (fun t ht => S.dN ht)
  intro t ht
  have ht' : t ∈ Ici s0 := mem_Ici.2 (le_of_lt ht)
  have := Dq_upper (S.N_ball ht')
  have := S.N_pos ht'
  exact div_neg_of_neg_of_pos (by linarith) (S.tpos ht')

/-- N² t is nonincreasing, so N → 0. -/
theorem N_tendsto : Tendsto (fun t => Nw (U t - 1) (V t - 2)) atTop (𝓝 0) := by
  have hm : AntitoneOn (fun t => Nw (U t - 1) (V t - 2) ^ 2 * t) (Ici s0) := by
    apply antiOn_Ici (f' := fun t => 2 * Nw (U t - 1) (V t - 2) * (Dq (U t - 1) (V t - 2) / t) * t
      + Nw (U t - 1) (V t - 2) ^ 2 * 1)
    · intro t ht
      have h := ((S.dN ht).pow 2).mul (hasDerivAt_id' t)
      exact h.congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)
    · intro t ht
      have htp := S.tpos (mem_Ici.2 (le_of_lt ht))
      have hb := S.N_ball (mem_Ici.2 (le_of_lt ht))
      have hl := Dq_upper hb
      have hN := Checked.Math.BEOCell.Nw_nonneg (U t - 1) (V t - 2)
      have e : 2 * Nw (U t - 1) (V t - 2) * (Dq (U t - 1) (V t - 2) / t) * t
          + Nw (U t - 1) (V t - 2) ^ 2 * 1 =
          Nw (U t - 1) (V t - 2) * (2 * Dq (U t - 1) (V t - 2) + Nw (U t - 1) (V t - 2)) := by
        field_simp; try ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos hN (by linarith)
  set C := Nw (U s0 - 1) (V s0 - 2) ^ 2 * s0 with hC
  have hsq : Tendsto (fun t => Nw (U t - 1) (V t - 2) ^ 2) atTop (𝓝 0) := by
    have hCt : Tendsto (fun t : ℝ => C / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) _ hCt
    filter_upwards [eventually_ge_atTop s0, eventually_gt_atTop 0] with t ht htp
    have h := hm (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
    simp only at h
    rw [le_div_iff₀ htp]; linarith
  have := hsq.sqrt
  simp only [Real.sqrt_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop s0] with t ht
  rw [Real.sqrt_sq (Checked.Math.BEOCell.Nw_nonneg _ _)]

theorem U_tendsto : Tendsto U atTop (𝓝 1) := by
  have h := S.N_tendsto.sqrt
  rw [Real.sqrt_zero] at h
  have h2 : Tendsto (fun t => U t - 1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ h
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact Real.abs_le_sqrt (x_sq_le_Nw _ _)
  have := h2.add_const 1
  simpa using this

theorem V_tendsto : Tendsto V atTop (𝓝 2) := by
  have h := S.N_tendsto.sqrt
  rw [Real.sqrt_zero] at h
  have h2 : Tendsto (fun t => V t - 2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ h
    exact Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact y_abs_le _ _
  have := h2.add_const 2
  simpa using this

theorem UV_pos {t : ℝ} (ht : t ∈ Ici s0) : 0 < U t ∧ 0 < V t := by
  obtain ⟨hx, hy⟩ := ball (S.N_ball ht)
  have := abs_le.1 hx; have := abs_le.1 hy
  constructor <;> linarith

/-- The sign function g = 2u − v and its derivative. -/
theorem dg {t : ℝ} (ht : t ∈ Ici s0) :
    HasDerivAt (fun t => 2 * U t - V t)
      (2 * (U t * (3 - U t - V t) / t) - V t * (U t - 1) / t) t :=
  ((S.hU t ht).const_mul 2).sub (S.hV t ht)

theorem contg : ContinuousOn (fun t => 2 * U t - V t) (Ici s0) :=
  fun t ht => (S.dg ht).continuousAt.continuousWithinAt

/-- At a zero of g: the derivative is 8u(1 − u)/t, `Nw = 32 (u − 1)²` and u ≠ 1. -/
theorem at_zero {z : ℝ} (hz : z ∈ Ici s0) (hg : 2 * U z - V z = 0) :
    Nw (U z - 1) (V z - 2) = 32 * (U z - 1) ^ 2 ∧ U z ≠ 1 ∧
    2 * (U z * (3 - U z - V z) / z) - V z * (U z - 1) / z = 8 * U z * (1 - U z) / z := by
  have hv : V z = 2 * U z := by linarith
  have hN : Nw (U z - 1) (V z - 2) = 32 * (U z - 1) ^ 2 := by rw [hv]; unfold Nw; ring
  refine ⟨hN, ?_, ?_⟩
  · intro h1
    have := S.N_pos hz
    rw [hN, h1] at this; norm_num at this
  · rw [hv]; ring

/-- Local sign of g at a zero, from the sign of its derivative. -/
theorem local_sign {z : ℝ} (hz : z ∈ Ici s0) (hg : 2 * U z - V z = 0) :
    ∃ δ > 0, (U z < 1 → (∀ y ∈ Ioo z (z + δ), 0 < 2 * U y - V y) ∧
        (∀ y ∈ Ioo (z - δ) z, 2 * U y - V y < 0)) ∧
      (1 < U z → (∀ y ∈ Ioo z (z + δ), 2 * U y - V y < 0) ∧
        (∀ y ∈ Ioo (z - δ) z, 0 < 2 * U y - V y)) := by
  obtain ⟨-, hU1, hd⟩ := S.at_zero hz hg
  have hzp := S.tpos hz
  have hUp := (S.UV_pos hz).1
  set d := 8 * U z * (1 - U z) / z with hd'
  have hD := S.dg hz
  rw [hd] at hD
  have hsl := hasDerivAt_iff_tendsto_slope.1 hD
  have hd0 : d ≠ 0 := by
    rw [hd']; apply div_ne_zero _ hzp.ne'
    apply mul_ne_zero (by positivity); intro h; apply hU1; linarith
  have key : ∀ᶠ y in 𝓝[≠] z, 0 < d * slope (fun t => 2 * U t - V t) z y := by
    have : Tendsto (fun y => d * slope (fun t => 2 * U t - V t) z y) (𝓝[≠] z) (𝓝 (d * d)) :=
      hsl.const_mul d
    exact this.eventually (lt_mem_nhds (mul_self_pos.2 hd0))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 key
  have P : ∀ y, |y - z| < ε → y ≠ z → 0 < d * (2 * U y - V y) * (y - z) := by
    intro y hy hne
    have hm : y ∈ Metric.ball z ε ∩ {z}ᶜ := ⟨by rwa [Metric.mem_ball, Real.dist_eq], hne⟩
    have h := hball hm
    simp only [mem_setOf_eq, slope_def_field, hg, sub_zero] at h
    have hw : y - z ≠ 0 := sub_ne_zero.2 hne
    have e : d * (2 * U y - V y) * (y - z) = d * ((2 * U y - V y) / (y - z)) * (y - z) ^ 2 := by
      field_simp
    rw [e]; exact mul_pos h (by positivity)
  have hd1 : U z < 1 → 0 < d := fun h => by
    rw [hd']; apply div_pos _ hzp; apply mul_pos (by positivity); linarith
  have hd2 : 1 < U z → d < 0 := fun h => by
    rw [hd']; apply div_neg_of_neg_of_pos _ hzp; apply mul_neg_of_pos_of_neg (by positivity); linarith
  refine ⟨ε, hε, fun hlt => ⟨fun y hy => ?_, fun y hy => ?_⟩, fun hlt => ⟨fun y hy => ?_, fun y hy => ?_⟩⟩
  · have h := P y (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]) (ne_of_gt hy.1)
    have := hd1 hlt; have : 0 < y - z := by linarith [hy.1]
    by_contra hc; push Not at hc; nlinarith [mul_pos (hd1 hlt) this]
  · have h := P y (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]) (ne_of_lt hy.2)
    have := hd1 hlt; have : y - z < 0 := by linarith [hy.2]
    by_contra hc; push Not at hc; nlinarith [mul_neg_of_pos_of_neg (hd1 hlt) this]
  · have h := P y (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]) (ne_of_gt hy.1)
    have := hd2 hlt; have : 0 < y - z := by linarith [hy.1]
    by_contra hc; push Not at hc; nlinarith [mul_neg_of_neg_of_pos (hd2 hlt) this]
  · have h := P y (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]) (ne_of_lt hy.2)
    have := hd2 hlt; have : y - z < 0 := by linarith [hy.2]
    by_contra hc; push Not at hc; nlinarith [mul_pos_of_neg_of_neg (hd2 hlt) this]

end Sys

/-! ### Sign changes -/

theorem same_sign {g : ℝ → ℝ} {I : Set ℝ} [I.OrdConnected] (hc : ContinuousOn g I)
    (hne : ∀ y ∈ I, g y ≠ 0) {y0 y1 : ℝ} (h0 : y0 ∈ I) (h1 : y1 ∈ I) (hpos : 0 < g y0) : 0 < g y1 := by
  by_contra hc'
  push Not at hc'
  have hsub : uIcc y0 y1 ⊆ I := Set.OrdConnected.uIcc_subset ‹_› h0 h1
  obtain ⟨c, hc1, hc2⟩ := intermediate_value_uIcc (hc.mono hsub)
    (show (0 : ℝ) ∈ uIcc (g y0) (g y1) from Set.mem_uIcc.2 (Or.inr ⟨hc', hpos.le⟩))
  exact hne c (hsub hc1) hc2

theorem same_sign_neg {g : ℝ → ℝ} {I : Set ℝ} [I.OrdConnected] (hc : ContinuousOn g I)
    (hne : ∀ y ∈ I, g y ≠ 0) {y0 y1 : ℝ} (h0 : y0 ∈ I) (h1 : y1 ∈ I) (hneg : g y0 < 0) : g y1 < 0 := by
  have := same_sign (g := fun y => -g y) hc.neg (fun y hy h => hne y hy (by linarith [h])) h0 h1
    (by linarith)
  linarith

namespace Sys
variable {U V : ℝ → ℝ} {s0 : ℝ} (S : Sys U V s0)
include S

theorem dpsi {t : ℝ} (ht : t ∈ Ici s0) (hg : 2 * U t - V t ≠ 0) :
    HasDerivAt (fun t => (U t - 1) / (2 * U t - V t))
      (Lq (U t - 1) (V t - 2) / (t * (2 * U t - V t) ^ 2)) t := by
  have h := ((S.hU t ht).sub_const 1).div (S.dg ht) hg
  have htp := (S.tpos ht).ne'
  exact h.congr_deriv (by unfold Lq; field_simp; ring)

theorem dchi {t : ℝ} (ht : t ∈ Ici s0) (hx : U t - 1 ≠ 0) :
    HasDerivAt (fun t => -(2 * U t - V t) / (U t - 1))
      (Lq (U t - 1) (V t - 2) / (t * (U t - 1) ^ 2)) t := by
  have h := (S.dg ht).neg.div ((S.hU t ht).sub_const 1) hx
  have htp := (S.tpos ht).ne'
  exact h.congr_deriv (by simp only [Pi.neg_apply]; unfold Lq; field_simp; ring)

/-- g = 2u − v vanishes somewhere after any radius: the ratio (u − 1)/g turns at a rate ≥ 1/(10 t). -/
theorem crosses {a : ℝ} (ha : a ∈ Ici s0) : ∃ z ∈ Ici a, 2 * U z - V z = 0 := by
  by_contra hc
  push Not at hc
  have hsub : Ici a ⊆ Ici s0 := Ici_subset_Ici.2 ha
  have hap : 0 < a := S.tpos ha
  set ψ : ℝ → ℝ := fun t => (U t - 1) / (2 * U t - V t) with hψ
  have hΨ : MonotoneOn (fun t => ψ t - Real.log t / 10) (Ici a) := by
    apply monoOn_Ici (f' := fun t => Lq (U t - 1) (V t - 2) / (t * (2 * U t - V t) ^ 2) - t⁻¹ / 10)
    · intro t ht
      exact (S.dpsi (hsub ht) (hc t ht)).sub
        ((Real.hasDerivAt_log (S.tpos (hsub ht)).ne').div_const 10)
    · intro t ht
      have ht' : t ∈ Ici a := mem_Ici.2 (le_of_lt ht)
      have htp := S.tpos (hsub ht')
      have hL := Lq_lower (S.N_ball (hsub ht'))
      have hg5 := g_sq_le (U t - 1) (V t - 2)
      have e : 2 * (U t - 1) - (V t - 2) = 2 * U t - V t := by ring
      rw [e] at hg5
      have hg2 : 0 < (2 * U t - V t) ^ 2 := by have := hc t ht'; positivity
      have : t⁻¹ / 10 ≤ Lq (U t - 1) (V t - 2) / (t * (2 * U t - V t) ^ 2) := by
        rw [inv_eq_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  set p := ψ a
  set t1 := a * Real.exp (10 * (|p| + 1)) with ht1
  have ht1a : a ≤ t1 := le_mul_of_one_le_right hap.le (Real.one_le_exp (by positivity))
  have hlog1 : Real.log t1 = Real.log a + 10 * (|p| + 1) := by
    rw [ht1, Real.log_mul hap.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hψ1 : ∀ t ∈ Ici t1, 1 ≤ ψ t := by
    intro t ht
    have h := hΨ (mem_Ici.2 le_rfl) (mem_Ici.2 (ht1a.trans ht)) (ht1a.trans ht)
    have hl : Real.log t1 ≤ Real.log t := Real.log_le_log (by linarith) ht
    simp only at h
    have := le_abs_self p; have := neg_abs_le p
    linarith
  have hsub1 : Ici t1 ⊆ Ici a := Ici_subset_Ici.2 ht1a
  have hx : ∀ t ∈ Ici t1, U t - 1 ≠ 0 := by
    intro t ht h0
    have := hψ1 t ht
    simp only [hψ, h0, zero_div] at this; norm_num at this
  set χ : ℝ → ℝ := fun t => -(2 * U t - V t) / (U t - 1) with hχ
  have hχψ : ∀ t ∈ Ici t1, χ t = -1 / ψ t := by
    intro t ht
    have h1 := hx t ht; have h2 := hc t (hsub1 ht)
    simp only [hχ, hψ]; field_simp
  have hX : MonotoneOn (fun t => χ t - Real.log t / 2) (Ici t1) := by
    apply monoOn_Ici (f' := fun t => Lq (U t - 1) (V t - 2) / (t * (U t - 1) ^ 2) - t⁻¹ / 2)
    · intro t ht
      exact (S.dchi (hsub (hsub1 ht)) (hx t ht)).sub
        ((Real.hasDerivAt_log (S.tpos (hsub (hsub1 ht))).ne').div_const 2)
    · intro t ht
      have ht' : t ∈ Ici t1 := mem_Ici.2 (le_of_lt ht)
      have htp := S.tpos (hsub (hsub1 ht'))
      have hL := Lq_lower (S.N_ball (hsub (hsub1 ht')))
      have hx2 : 0 < (U t - 1) ^ 2 := by have := hx t ht'; positivity
      have : t⁻¹ / 2 ≤ Lq (U t - 1) (V t - 2) / (t * (U t - 1) ^ 2) := by
        rw [inv_eq_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (V t - 2)]
      linarith
  set t2 := t1 * Real.exp 4 with ht2
  have ht1p : 0 < t1 := lt_of_lt_of_le hap ht1a
  have ht12 : t1 ≤ t2 := le_mul_of_one_le_right ht1p.le (Real.one_le_exp (by norm_num))
  have hlog2 : Real.log t2 = Real.log t1 + 4 := by
    rw [ht2, Real.log_mul ht1p.ne' (Real.exp_pos _).ne', Real.log_exp]
  have h := hX (mem_Ici.2 le_rfl) (mem_Ici.2 ht12) ht12
  simp only at h
  rw [hχψ t1 (mem_Ici.2 le_rfl), hχψ t2 (mem_Ici.2 ht12)] at h
  have a1 := hψ1 t1 (mem_Ici.2 le_rfl)
  have a2 := hψ1 t2 (mem_Ici.2 ht12)
  have b1 : -1 ≤ -1 / ψ t1 := by
    rw [neg_div, neg_le_neg_iff, div_le_one (by linarith)]; exact a1
  have b2 : -1 / ψ t2 < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
  linarith

theorem next_of_ne {a : ℝ} (ha : a ∈ Ici s0) (hga : 2 * U a - V a ≠ 0) :
    ∃ z, a < z ∧ 2 * U z - V z = 0 ∧ ∀ y ∈ Ico a z, 2 * U y - V y ≠ 0 := by
  set Z := Ici a ∩ (fun t => 2 * U t - V t) ⁻¹' {0} with hZ
  obtain ⟨z0, hz0, hgz0⟩ := S.crosses ha
  have hne : Z.Nonempty := ⟨z0, hz0, by simpa using hgz0⟩
  have hcl : IsClosed Z :=
    (S.contg.mono (Ici_subset_Ici.2 ha)).preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hbdd : BddBelow Z := ⟨a, fun z hz => hz.1⟩
  have hm := hcl.csInf_mem hne hbdd
  have hm2 : 2 * U (sInf Z) - V (sInf Z) = 0 := by simpa using hm.2
  refine ⟨sInf Z, lt_of_le_of_ne hm.1 (fun h => hga (h ▸ hm2)), hm2, fun y hy hy0 => ?_⟩
  have : sInf Z ≤ y := csInf_le hbdd ⟨hy.1, by simpa using hy0⟩
  linarith [hy.2]

theorem next {a : ℝ} (ha : a ∈ Ici s0) :
    ∃ z, a < z ∧ 2 * U z - V z = 0 ∧ ∀ y ∈ Ioo a z, 2 * U y - V y ≠ 0 := by
  by_cases hga : 2 * U a - V a = 0
  · obtain ⟨δ, hδ, h1, h2⟩ := S.local_sign ha hga
    have hU1 := (S.at_zero ha hga).2.1
    have hloc : ∀ y ∈ Ioo a (a + δ), 2 * U y - V y ≠ 0 := by
      intro y hy
      rcases lt_or_gt_of_ne hU1 with h | h
      · exact ((h1 h).1 y hy).ne'
      · exact ((h2 h).1 y hy).ne
    have ha' : a + δ / 2 ∈ Ici s0 := mem_Ici.2 (by have := ha.out; linarith)
    obtain ⟨z, hz1, hz2, hz3⟩ := S.next_of_ne ha' (hloc _ ⟨by linarith, by linarith⟩)
    refine ⟨z, by linarith, hz2, fun y hy => ?_⟩
    by_cases hy' : y < a + δ / 2
    · exact hloc y ⟨hy.1, by linarith⟩
    · exact hz3 y ⟨by linarith, hy.2⟩
  · obtain ⟨z, hz1, hz2, hz3⟩ := S.next_of_ne ha hga
    exact ⟨z, hz1, hz2, fun y hy => hz3 y ⟨hy.1.le, hy.2⟩⟩

/-- One segment between consecutive zeros: the sign of g and the side of the next zero. -/
theorem seg {a z : ℝ} (ha : a ∈ Ici s0) (hga : 2 * U a - V a = 0) (haz : a < z)
    (hgz : 2 * U z - V z = 0) (hne : ∀ y ∈ Ioo a z, 2 * U y - V y ≠ 0) :
    (U a < 1 → (∀ y ∈ Ioo a z, 0 < 2 * U y - V y) ∧ 1 < U z) ∧
    (1 < U a → (∀ y ∈ Ioo a z, 2 * U y - V y < 0) ∧ U z < 1) := by
  have hz : z ∈ Ici s0 := mem_Ici.2 (by have := ha.out; linarith)
  obtain ⟨δ, hδ, h1, h2⟩ := S.local_sign ha hga
  obtain ⟨δ', hδ', h1', h2'⟩ := S.local_sign hz hgz
  have hUz := (S.at_zero hz hgz).2.1
  have hc : ContinuousOn (fun t => 2 * U t - V t) (Ioo a z) :=
    S.contg.mono fun y hy => mem_Ici.2 (by have := ha.out; linarith [hy.1])
  set y0 := a + min δ (z - a) / 2 with hy0
  have hm1 : min δ (z - a) ≤ δ := min_le_left _ _
  have hm2 : min δ (z - a) ≤ z - a := min_le_right _ _
  have hm3 : 0 < min δ (z - a) := lt_min hδ (by linarith)
  have hy0I : y0 ∈ Ioo a z := ⟨by linarith, by linarith⟩
  have hy0J : y0 ∈ Ioo a (a + δ) := ⟨by linarith, by linarith⟩
  set y1 := z - min δ' (z - a) / 2 with hy1
  have hn1 : min δ' (z - a) ≤ δ' := min_le_left _ _
  have hn2 : min δ' (z - a) ≤ z - a := min_le_right _ _
  have hn3 : 0 < min δ' (z - a) := lt_min hδ' (by linarith)
  have hy1I : y1 ∈ Ioo a z := ⟨by linarith, by linarith⟩
  have hy1J : y1 ∈ Ioo (z - δ') z := ⟨by linarith, by linarith⟩
  constructor
  · intro hlt
    have hpos : ∀ y ∈ Ioo a z, 0 < 2 * U y - V y := fun y hy =>
      same_sign (g := fun t => 2 * U t - V t) hc hne hy0I hy (((h1 hlt).1) y0 hy0J)
    refine ⟨hpos, ?_⟩
    rcases lt_or_gt_of_ne hUz with h | h
    · exact absurd ((h1' h).2 y1 hy1J) (not_lt.2 (hpos y1 hy1I).le)
    · exact h
  · intro hlt
    have hneg : ∀ y ∈ Ioo a z, 2 * U y - V y < 0 := fun y hy =>
      same_sign_neg (g := fun t => 2 * U t - V t) hc hne hy0I hy (((h2 hlt).1) y0 hy0J)
    refine ⟨hneg, ?_⟩
    rcases lt_or_gt_of_ne hUz with h | h
    · exact h
    · exact absurd ((h2' h).2 y1 hy1J) (not_lt.2 (hneg y1 hy1I).le)

/-- The first segment, from s0 where g < 0. -/
theorem seg0 {z : ℝ} (hg0 : 2 * U s0 - V s0 < 0) (hz0 : s0 < z) (hgz : 2 * U z - V z = 0)
    (hne : ∀ y ∈ Ioo s0 z, 2 * U y - V y ≠ 0) :
    (∀ y ∈ Ico s0 z, 2 * U y - V y < 0) ∧ U z < 1 := by
  have hz : z ∈ Ici s0 := mem_Ici.2 hz0.le
  obtain ⟨δ', hδ', h1', h2'⟩ := S.local_sign hz hgz
  have hUz := (S.at_zero hz hgz).2.1
  have hc : ContinuousOn (fun t => 2 * U t - V t) (Ico s0 z) := S.contg.mono fun y hy => mem_Ici.2 hy.1
  have hne' : ∀ y ∈ Ico s0 z, 2 * U y - V y ≠ 0 := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h]; exact hg0.ne
    · exact hne y ⟨h, hy.2⟩
  have hneg : ∀ y ∈ Ico s0 z, 2 * U y - V y < 0 := fun y hy =>
    same_sign_neg (g := fun t => 2 * U t - V t) hc hne' ⟨le_rfl, hz0⟩ hy hg0
  refine ⟨hneg, ?_⟩
  set y1 := z - min δ' (z - s0) / 2 with hy1
  have hn1 : min δ' (z - s0) ≤ δ' := min_le_left _ _
  have hn2 : min δ' (z - s0) ≤ z - s0 := min_le_right _ _
  have hn3 : 0 < min δ' (z - s0) := lt_min hδ' (by linarith)
  rcases lt_or_gt_of_ne hUz with h | h
  · exact h
  · exact absurd ((h2' h).2 y1 ⟨by linarith, by linarith⟩) (not_lt.2 (hneg y1 ⟨by linarith, by linarith⟩).le)

end Sys

theorem tail {U V : ℝ → ℝ} {s0 : ℝ} (hs0 : 0 < s0)
    (hU : ∀ t ∈ Ici s0, HasDerivAt U (U t * (3 - U t - V t) / t) t)
    (hV : ∀ t ∈ Ici s0, HasDerivAt V (V t * (U t - 1) / t) t)
    (hN0 : Nw (U s0 - 1) (V s0 - 2) ≤ 1 / 400) (hNpos : 0 < Nw (U s0 - 1) (V s0 - 2))
    (hg0 : 2 * U s0 - V s0 < 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧ s0 < ζ 0 ∧
      (∀ t ∈ Ico s0 (ζ 0), 2 * U t - V t < 0) ∧
      (∀ k, 2 * U (ζ k) - V (ζ k) = 0) ∧
      (∀ k, ∀ t ∈ Ioo (ζ (2 * k)) (ζ (2 * k + 1)), 0 < 2 * U t - V t) ∧
      (∀ k, ∀ t ∈ Ioo (ζ (2 * k + 1)) (ζ (2 * k + 2)), 2 * U t - V t < 0) ∧
      (∀ k, U (ζ (2 * k)) < 1 ∧ 1 < U (ζ (2 * k + 1))) ∧
      (∀ k, |U (ζ (k + 1)) - 1| < |U (ζ k) - 1|) ∧
      (∀ k, 32 * (U (ζ k) - 1) ^ 2 ≤ Nw (U s0 - 1) (V s0 - 2)) ∧
      (∀ t ∈ Ici s0, 0 < U t ∧ 0 < V t) ∧
      Tendsto U atTop (𝓝 1) ∧ Tendsto V atTop (𝓝 2) := by
  have S : Sys U V s0 := ⟨hs0, hU, hV, hN0, hNpos⟩
  have NEXT : ∀ a : ℝ, ∃ z : ℝ, a ∈ Ici s0 →
      a < z ∧ 2 * U z - V z = 0 ∧ ∀ y ∈ Ioo a z, 2 * U y - V y ≠ 0 := by
    intro a
    by_cases ha : a ∈ Ici s0
    · obtain ⟨z, h⟩ := S.next ha; exact ⟨z, fun _ => h⟩
    · exact ⟨a, fun h => absurd h ha⟩
  choose nx hnx using NEXT
  let ζ : ℕ → ℝ := fun k => Nat.rec (nx s0) (fun _ z => nx z) k
  have hζ0 : ζ 0 = nx s0 := rfl
  have hζs : ∀ k, ζ (k + 1) = nx (ζ k) := fun k => rfl
  have A : ∀ k, s0 < ζ k := by
    intro k
    induction k with
    | zero => rw [hζ0]; exact (hnx s0 (mem_Ici.2 le_rfl)).1
    | succ k ih => rw [hζs]; exact ih.trans (hnx (ζ k) (mem_Ici.2 ih.le)).1
  have Ai : ∀ k, ζ k ∈ Ici s0 := fun k => mem_Ici.2 (A k).le
  have lt : ∀ k, ζ k < ζ (k + 1) := fun k => by rw [hζs]; exact (hnx (ζ k) (Ai k)).1
  have zero : ∀ k, 2 * U (ζ k) - V (ζ k) = 0 := by
    intro k; cases k with
    | zero => rw [hζ0]; exact (hnx s0 (mem_Ici.2 le_rfl)).2.1
    | succ k => rw [hζs]; exact (hnx (ζ k) (Ai k)).2.1
  have gap : ∀ k, ∀ y ∈ Ioo (ζ k) (ζ (k + 1)), 2 * U y - V y ≠ 0 := fun k => by
    rw [hζs]; exact (hnx (ζ k) (Ai k)).2.2
  have gap0 : ∀ y ∈ Ioo s0 (ζ 0), 2 * U y - V y ≠ 0 := by
    rw [hζ0]; exact (hnx s0 (mem_Ici.2 le_rfl)).2.2
  have base := S.seg0 hg0 (A 0) (zero 0) gap0
  have sg := fun k => S.seg (Ai k) (zero k) (lt k) (zero (k + 1)) (gap k)
  have par : ∀ k, U (ζ (2 * k)) < 1 ∧ 1 < U (ζ (2 * k + 1)) := by
    intro k
    induction k with
    | zero => exact ⟨base.2, ((sg 0).1 base.2).2⟩
    | succ k ih =>
      have e1 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      have h2 : U (ζ (2 * (k + 1))) < 1 := by rw [e1]; exact ((sg (2 * k + 1)).2 ih.2).2
      refine ⟨h2, ?_⟩
      have := ((sg (2 * (k + 1))).1 h2).2
      exact this
  have hmono : StrictMono ζ := strictMono_nat_of_lt_succ lt
  refine ⟨ζ, hmono, ?_, A 0, base.1, zero, fun k => ((sg (2 * k)).1 (par k).1).1,
    fun k => ((sg (2 * k + 1)).2 (par k).2).1, par, ?_, ?_, fun t ht => S.UV_pos ht,
    S.U_tendsto, S.V_tendsto⟩
  · -- the zeros do not accumulate
    apply tendsto_atTop_atTop_of_monotone' hmono.monotone
    intro hbdd
    set L := ⨆ i, ζ i with hL
    have hlim : Tendsto ζ atTop (𝓝 L) := tendsto_atTop_ciSup hmono.monotone hbdd
    have hζL : ∀ k, ζ k < L := fun k => lt_of_lt_of_le (lt k) (le_ciSup hbdd (k + 1))
    have hLs : L ∈ Ici s0 := mem_Ici.2 ((A 0).le.trans (hζL 0).le)
    have hgL : 2 * U L - V L = 0 := by
      have hc : Tendsto (fun k => 2 * U (ζ k) - V (ζ k)) atTop (𝓝 (2 * U L - V L)) :=
        ((S.dg hLs).continuousAt.tendsto).comp hlim
      have h0 : (fun k => 2 * U (ζ k) - V (ζ k)) = fun _ => (0 : ℝ) := funext zero
      rw [h0] at hc
      exact (tendsto_nhds_unique hc tendsto_const_nhds)
    obtain ⟨δ, hδ, h1, h2⟩ := S.local_sign hLs hgL
    have hUL := (S.at_zero hLs hgL).2.1
    obtain ⟨k, hk⟩ := (hlim.eventually (Ioi_mem_nhds (show L - δ < L by linarith))).exists
    have hy : ζ k ∈ Ioo (L - δ) L := ⟨hk, hζL k⟩
    rcases lt_or_gt_of_ne hUL with h | h
    · exact absurd (zero k) ((h1 h).2 _ hy).ne
    · exact absurd (zero k) ((h2 h).2 _ hy).ne'
  · intro k
    have h := S.N_anti (Ai k) (Ai (k + 1)) (lt k)
    simp only at h
    rw [(S.at_zero (Ai k) (zero k)).1, (S.at_zero (Ai (k + 1)) (zero (k + 1))).1] at h
    exact sq_lt_sq.1 (by linarith)
  · intro k
    rw [← (S.at_zero (Ai k) (zero k)).1]
    exact S.N_le (Ai k)

end Work.Math.BEFocus
