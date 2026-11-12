import Checked.Trust.NecessityO
import Checked.Chemistry.SRKExists
import Checked.Chemistry.RKExists
import Mathlib.Analysis.Convex.Deriv

/-!
# Every Maxwell coexistence state of a subcritical RK-form isotherm lies right of the co-volume
(run 2026-11-12T1228Z)

For the isotherm p(v) = c/(v − b) − a/(v² + b v) with c = R T > 0, a > 0, b > 0 and c b < a, every
Maxwell coexistence state (v_l < v_g, p(v_l) = p(v_g) = p_s, ∫ p = p_s (v_g − v_l)) has v_l > b.
So the hypothesis `b < v_l` of the RK and SRK acentric-factor uniqueness theorems is redundant.

Proof: if an interval [v_l, v_g] with v_l ≤ b contains a pole (b, 0 or −b), Lean's integral is 0,
so p_s = 0 and p(v_l) = 0, but p has no zero at or left of b (junk values included). Otherwise the
interval lies in one of (−∞, −b), (−b, 0), (0, b): p is strictly concave on the first and last
(p'' < 0 where v² + b v > 0 and v < b) and strictly convex on the middle one (c b < 16 a), and a
strictly concave (convex) function equal to p_s at both ends has integral above (below)
p_s (v_g − v_l).
-/

open Set Filter Topology

namespace Checked.Trust.MaxwellRight
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence Checked.Trust.NecessityO

/-- A strictly concave function equal to `ps` at both ends of `[x, y]` has integral above
`ps (y − x)`. -/
theorem integral_gt_of_strictConcave {p : ℝ → ℝ} {x y ps : ℝ} (hxy : x < y)
    (hc : ContinuousOn p (Icc x y)) (hf : StrictConcaveOn ℝ (Icc x y) p) (hx : p x = ps) (hy : p y = ps) :
    ps * (y - x) < ∫ v in x..y, p v := by
  have key : ∀ z ∈ Ioo x y, ps < p z := by
    intro z hz
    have ha : 0 < (y - z) / (y - x) := div_pos (by linarith [hz.2]) (by linarith)
    have hb : 0 < (z - x) / (y - x) := div_pos (by linarith [hz.1]) (by linarith)
    have hab : (y - z) / (y - x) + (z - x) / (y - x) = 1 := by field_simp; ring
    have := hf.2 (left_mem_Icc.2 hxy.le) (right_mem_Icc.2 hxy.le) hxy.ne ha hb hab
    have hyx : y - x ≠ 0 := by linarith
    have hz' : ((y - z) / (y - x)) • x + ((z - x) / (y - x)) • y = z := by
      simp only [smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hyx]; ring
    rw [hz', hx, hy, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul] at this
    exact this
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hxy
    continuousOn_const hc (fun z hz => by
      rcases eq_or_lt_of_le hz.2 with h | h
      · rw [h, hy]
      · exact (key z ⟨hz.1, h⟩).le)
    ⟨(x + y) / 2, ⟨by linarith, by linarith⟩, key _ ⟨by linarith, by linarith⟩⟩
  simpa [mul_comm] using h

/-- A strictly convex function equal to `ps` at both ends of `[x, y]` has integral below
`ps (y − x)`. -/
theorem integral_lt_of_strictConvex {p : ℝ → ℝ} {x y ps : ℝ} (hxy : x < y)
    (hc : ContinuousOn p (Icc x y)) (hf : StrictConvexOn ℝ (Icc x y) p) (hx : p x = ps) (hy : p y = ps) :
    ∫ v in x..y, p v < ps * (y - x) := by
  have h := integral_gt_of_strictConcave (p := fun v => -p v) (ps := -ps) hxy hc.neg hf.neg
    (by simp [hx]) (by simp [hy])
  rw [intervalIntegral.integral_neg] at h
  linarith

section RKForm
variable (c a b : ℝ)

/-- The RK-form isotherm c/(v − b) − a/(v² + b v), written as `cubicP` with u = 1, w = 0. -/
theorem cubicP_rk (R T a b v : ℝ) :
    cubicP R a b 1 0 T v = R * T / (v - b) - a / (v ^ 2 + 1 * b * v + 0 * b ^ 2) := rfl

/-- First derivative of the RK-form isotherm. -/
noncomputable def p1 (v : ℝ) : ℝ :=
  -(c) / (v - b) ^ 2 + a * (2 * v + 1 * b) / (v ^ 2 + 1 * b * v + 0 * b ^ 2) ^ 2

/-- Second derivative of the RK-form isotherm. -/
noncomputable def p2 (v : ℝ) : ℝ :=
  2 * c / (v - b) ^ 3 + 2 * a * ((v ^ 2 + b * v) - (2 * v + b) ^ 2) / (v ^ 2 + b * v) ^ 3

theorem hasDerivAt_p1 {v : ℝ} (hv : v - b ≠ 0) (hD : v ^ 2 + b * v ≠ 0) :
    HasDerivAt (p1 c a b) (p2 c a b v) v := by
  have h1 : HasDerivAt (fun x => x - b) 1 v := (hasDerivAt_id v).sub_const b
  have hD' : HasDerivAt (fun x => x ^ 2 + 1 * b * x + 0 * b ^ 2) (2 * v + b) v := by
    have := (((hasDerivAt_pow 2 v).add ((hasDerivAt_id v).const_mul (1 * b))).add_const (0 * b ^ 2))
    convert this using 1; simp; ring
  have hD0 : v ^ 2 + 1 * b * v + 0 * b ^ 2 ≠ 0 := by simpa using hD
  have hA := ((hasDerivAt_const v (-c)).div (h1.pow 2) (pow_ne_zero 2 hv))
  have hB := ((((hasDerivAt_id v).const_mul 2).add_const (1 * b)).const_mul a).div (hD'.pow 2)
    (pow_ne_zero 2 hD0)
  have := hA.add hB
  convert this using 1
  · ext x; simp only [p1, Pi.add_apply, Pi.div_apply, Pi.pow_apply, id]
  · unfold p2
    have hD1 : v ^ 2 + 1 * b * v + 0 * b ^ 2 = v ^ 2 + b * v := by ring
    simp only [Pi.pow_apply, id, hD1]
    generalize v - b = E at *
    generalize v ^ 2 + b * v = D at *
    field_simp
    ring

theorem p2_neg {v : ℝ} (hc : 0 < c) (ha : 0 < a) (hv : v < b) (hD : 0 < v ^ 2 + b * v) :
    p2 c a b v < 0 := by
  unfold p2
  have h1 : 2 * c / (v - b) ^ 3 < 0 :=
    div_neg_of_pos_of_neg (by linarith) (Odd.pow_neg (by decide) (by linarith))
  have h2 : 2 * a * ((v ^ 2 + b * v) - (2 * v + b) ^ 2) / (v ^ 2 + b * v) ^ 3 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by nlinarith [sq_nonneg (v + b / 2)]))
      (by positivity)
  linarith

theorem p2_pos {v : ℝ} (hb : 0 < b) (hc : 0 < c) (ha : 0 < a) (hcb : c * b < a) (h1 : -b < v) (h2 : v < 0) :
    0 < p2 c a b v := by
  unfold p2
  set q := -(v ^ 2 + b * v) with hq
  set s := (2 * v + b) ^ 2 - (v ^ 2 + b * v) with hs
  set r := b - v with hr
  have hq0 : 0 < q := by nlinarith
  have hq1 : q ≤ b ^ 2 / 4 := by nlinarith [sq_nonneg (v + b / 2)]
  have hs1 : b ^ 2 / 4 ≤ s := by nlinarith [sq_nonneg (v + b / 2)]
  have hr1 : b ≤ r := by linarith
  have e1 : 2 * c / (v - b) ^ 3 = -(2 * c / r ^ 3) := by
    rw [show v - b = -r by ring, neg_pow, show ((-1 : ℝ)) ^ 3 = -1 by norm_num, neg_one_mul, div_neg]
  have e2 : 2 * a * ((v ^ 2 + b * v) - (2 * v + b) ^ 2) / (v ^ 2 + b * v) ^ 3 = 2 * a * s / q ^ 3 := by
    rw [show v ^ 2 + b * v = -q by ring, show -q - (2 * v + b) ^ 2 = -s by rw [hs]; ring, neg_pow,
      show ((-1 : ℝ)) ^ 3 = -1 by norm_num, neg_one_mul, mul_neg, neg_div_neg_eq]
  rw [e1, e2]
  -- 2c/r³ ≤ 2c/b³ < 2a/b⁴ ≤ 32 a/b⁴ ≤ 2 a s/q³
  have hb3 : 0 < b ^ 3 := by positivity
  have k1 : 2 * c / r ^ 3 ≤ 2 * c / b ^ 3 :=
    div_le_div_of_nonneg_left (by linarith) hb3 (pow_le_pow_left₀ hb.le hr1 3)
  have k2 : 2 * c / b ^ 3 < 2 * a / b ^ 4 := by
    rw [div_lt_div_iff₀ hb3 (by positivity)]; nlinarith [pow_pos hb 3]
  have k3 : 2 * a / b ^ 4 ≤ 2 * a * s / q ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hq3 : q ^ 3 ≤ (b ^ 2 / 4) ^ 3 := pow_le_pow_left₀ hq0.le hq1 3
    have : 2 * a * q ^ 3 ≤ 2 * a * (b ^ 2 / 4) ^ 3 := by nlinarith
    have : 2 * a * (b ^ 2 / 4) ^ 3 ≤ 2 * a * s * b ^ 4 := by
      have : (b ^ 2 / 4) ^ 3 ≤ s * b ^ 4 := by
        have hb4 : 0 < b ^ 4 := by positivity
        nlinarith
      nlinarith
    linarith
  linarith

theorem hasDerivAt_p (R T a b v : ℝ) (hv : v - b ≠ 0) (hD : v ^ 2 + b * v ≠ 0) :
    HasDerivAt (cubicP R a b 1 0 T) (p1 (R * T) a b v) v :=
  hasDerivAt_P R a b 1 0 T v hv (by simpa using hD)

/-- On an open set avoiding the poles, the second derivative of the RK-form isotherm is `p2`. -/
theorem deriv2_eq (R T a b : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hUp : ∀ v ∈ U, v - b ≠ 0 ∧ v ^ 2 + b * v ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv^[2] (cubicP R a b 1 0 T) x = p2 (R * T) a b x := by
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
  have heq : deriv (cubicP R a b 1 0 T) =ᶠ[𝓝 x] p1 (R * T) a b := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hasDerivAt_p R T a b y (hUp y hy).1 (hUp y hy).2).deriv
  rw [heq.deriv_eq]
  exact (hasDerivAt_p1 (R * T) a b (hUp x hx).1 (hUp x hx).2).deriv

theorem continuousOn_p (R T a b : ℝ) {S : Set ℝ} (hUp : ∀ v ∈ S, v - b ≠ 0 ∧ v ^ 2 + b * v ≠ 0) :
    ContinuousOn (cubicP R a b 1 0 T) S := fun v hv =>
  (hasDerivAt_p R T a b v (hUp v hv).1 (hUp v hv).2).continuousAt.continuousWithinAt

/-- The RK-form isotherm has no zero at or left of the co-volume (junk values at b, 0, −b included). -/
theorem p_ne_zero (R T a b v : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < R * T) (hcb : R * T * b < a)
    (hv : v ≤ b) : cubicP R a b 1 0 T v ≠ 0 := by
  unfold cubicP
  rcases eq_or_lt_of_le hv with rfl | hv
  · rw [sub_self, div_zero, zero_sub, neg_ne_zero]
    exact div_ne_zero ha.ne' (by nlinarith)
  rcases lt_trichotomy v 0 with h0 | rfl | h0
  · rcases lt_trichotomy v (-b) with h1 | rfl | h1
    · intro h
      have hD : 0 < v ^ 2 + 1 * b * v + 0 * b ^ 2 := by nlinarith
      rw [sub_eq_zero, div_eq_div_iff (by linarith) hD.ne'] at h
      nlinarith
    · have : (-b) ^ 2 + 1 * b * (-b) + 0 * b ^ 2 = 0 := by ring
      rw [this, div_zero, sub_zero]
      exact div_ne_zero hc.ne' (by linarith)
    · intro h
      have hD : v ^ 2 + 1 * b * v + 0 * b ^ 2 < 0 := by nlinarith
      rw [sub_eq_zero, div_eq_div_iff (by linarith) hD.ne] at h
      nlinarith [mul_pos (show 0 < a - R * T * b by linarith) (show 0 < -v by linarith)]
  · simp only [ne_eq]
    rw [show (0 : ℝ) ^ 2 + 1 * b * 0 + 0 * b ^ 2 = 0 by ring, div_zero, sub_zero]
    exact div_ne_zero hc.ne' (by linarith)
  · intro h
    have hD : 0 < v ^ 2 + 1 * b * v + 0 * b ^ 2 := by nlinarith
    rw [sub_eq_zero, div_eq_div_iff (by linarith) hD.ne'] at h
    nlinarith [mul_pos hc hD]

/-- **Every Maxwell coexistence state of the RK-form isotherm lies right of the co-volume** when
R T > 0 and R T b < a. -/
theorem maxwell_right (R T a b vl vg ps : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < R * T)
    (hcb : R * T * b < a) (h : IsMaxwellCoexistence (cubicP R a b 1 0 T) vl vg ps) : b < vl := by
  by_contra hvl
  have hvl : vl ≤ b := not_lt.1 hvl
  obtain ⟨hlg, hpl, hpg, hint⟩ := h
  have nz := p_ne_zero R T a b vl ha hb hc hcb hvl
  by_cases hpole : b ∈ Icc vl vg ∨ (0 : ℝ) ∈ Icc vl vg ∨ -b ∈ Icc vl vg
  · have hni : ¬ IntervalIntegrable (cubicP R a b 1 0 T) MeasureTheory.volume vl vg := by
      have hu : ∀ c, c ∈ Icc vl vg → c ∈ uIcc vl vg := fun c hc => by rw [uIcc_of_le hlg.le]; exact hc
      rcases hpole with hp | hp | hp
      · refine not_ii_of_pole _ (fun x => -a / (x ^ 2 + 1 * b * x + 0 * b ^ 2)) (fun _ => 1) b (R * T)
          hc.ne' continuousAt_const one_ne_zero
          (continuousAt_const.div (by fun_prop) (by nlinarith))
          (Eventually.of_forall fun x => by unfold cubicP; ring) hlg.ne (hu _ hp)
      · refine not_ii_of_pole _ (fun x => R * T / (x - b)) (fun x => x + b) 0 (-a)
          (neg_ne_zero.2 ha.ne') (by fun_prop) (by simpa using hb.ne')
          (continuousAt_const.div (by fun_prop) (by simpa using hb.ne'))
          (Eventually.of_forall fun x => by unfold cubicP; ring) hlg.ne (hu _ hp)
      · refine not_ii_of_pole _ (fun x => R * T / (x - b)) (fun x => x) (-b) (-a)
          (neg_ne_zero.2 ha.ne') continuousAt_id (by simpa using hb.ne')
          (continuousAt_const.div (by fun_prop) (by intro h; linarith))
          (Eventually.of_forall fun x => by unfold cubicP; ring) hlg.ne (hu _ hp)
    rw [intervalIntegral.integral_undef hni] at hint
    have hps : ps = 0 := by
      have : ps * (vg - vl) = 0 := hint.symm
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (by linarith)
    exact nz (hpl.trans hps)
  · simp only [not_or, mem_Icc, not_and, not_le] at hpole
    obtain ⟨hpb, hp0, hpm⟩ := hpole
    have hvg : vg < b := hpb hvl
    have sub : ∀ (U : Set ℝ), Icc vl vg ⊆ U → (∀ v ∈ U, v - b ≠ 0 ∧ v ^ 2 + b * v ≠ 0) →
        ∀ v ∈ Icc vl vg, v - b ≠ 0 ∧ v ^ 2 + b * v ≠ 0 := fun U hs hU v hv => hU v (hs hv)
    -- the three pole-free components
    rcases lt_or_gt_of_ne (show vl ≠ -b by intro e; exact absurd (hpm (le_of_eq e)) (by linarith)) with h1 | h1
    · -- left of −b
      have hvg' : vg < -b := hpm h1.le
      have hU : ∀ v ∈ Iio (-b), v - b ≠ 0 ∧ v ^ 2 + b * v ≠ 0 := fun v (hv : v < -b) =>
        ⟨by linarith, by nlinarith⟩
      have hs : Icc vl vg ⊆ Iio (-b) := fun v hv => lt_of_le_of_lt hv.2 hvg'
      have hcc : StrictConcaveOn ℝ (Icc vl vg) (cubicP R a b 1 0 T) :=
        strictConcaveOn_of_deriv2_neg (convex_Icc _ _) (continuousOn_p R T a b (sub _ hs hU))
          (fun x hx => by
            rw [interior_Icc] at hx
            have hxU : x ∈ Iio (-b) := hs (Ioo_subset_Icc_self hx)
            rw [deriv2_eq R T a b isOpen_Iio hU hxU]
            exact p2_neg _ _ _ hc ha (by linarith [hxU.out]) (by nlinarith [hxU.out]))
      have := integral_gt_of_strictConcave hlg (continuousOn_p R T a b (sub _ hs hU)) hcc hpl hpg
      linarith
    · rcases lt_or_gt_of_ne (show vl ≠ 0 by intro e; exact absurd (hp0 (le_of_eq e)) (by linarith)) with h2 | h2
      · -- between −b and 0
        have hvg' : vg < 0 := hp0 h2.le
        have hU : ∀ v ∈ Ioo (-b) 0, v - b ≠ 0 ∧ v ^ 2 + b * v ≠ 0 := fun v hv =>
          ⟨by linarith [hv.2], by nlinarith [hv.1, hv.2]⟩
        have hs : Icc vl vg ⊆ Ioo (-b) 0 := fun v hv => ⟨lt_of_lt_of_le h1 hv.1, lt_of_le_of_lt hv.2 hvg'⟩
        have hcc : StrictConvexOn ℝ (Icc vl vg) (cubicP R a b 1 0 T) :=
          strictConvexOn_of_deriv2_pos (convex_Icc _ _) (continuousOn_p R T a b (sub _ hs hU))
            (fun x hx => by
              rw [interior_Icc] at hx
              have hxU : x ∈ Ioo (-b) 0 := hs (Ioo_subset_Icc_self hx)
              rw [deriv2_eq R T a b isOpen_Ioo hU hxU]
              exact p2_pos _ _ _ hb hc ha hcb hxU.1 hxU.2)
        have := integral_lt_of_strictConvex hlg (continuousOn_p R T a b (sub _ hs hU)) hcc hpl hpg
        linarith
      · -- between 0 and b
        have hU : ∀ v ∈ Ioo 0 b, v - b ≠ 0 ∧ v ^ 2 + b * v ≠ 0 := fun v hv =>
          ⟨by linarith [hv.2], by nlinarith [hv.1, hv.2]⟩
        have hs : Icc vl vg ⊆ Ioo 0 b := fun v hv => ⟨lt_of_lt_of_le h2 hv.1, lt_of_le_of_lt hv.2 hvg⟩
        have hcc : StrictConcaveOn ℝ (Icc vl vg) (cubicP R a b 1 0 T) :=
          strictConcaveOn_of_deriv2_neg (convex_Icc _ _) (continuousOn_p R T a b (sub _ hs hU))
            (fun x hx => by
              rw [interior_Icc] at hx
              have hxU : x ∈ Ioo 0 b := hs (Ioo_subset_Icc_self hx)
              rw [deriv2_eq R T a b isOpen_Ioo hU hxU]
              exact p2_neg _ _ _ hc ha hxU.2 (by nlinarith [hxU.1, hxU.2]))
        have := integral_gt_of_strictConcave hlg (continuousOn_p R T a b (sub _ hs hU)) hcc hpl hpg
        linarith

end RKForm

/-! ## The hypothesis `b < v_l` of the RK and SRK uniqueness theorems is redundant -/

/-- SRK at ω = 1: `b < v_l` (hypothesis 5) is redundant. The critical point gives R T_c > 0 and the
reduced coexistence temperature θ = R T b/a ≤ 0.0831 < 1 (`SRKExists.theta_bounds`), so every Maxwell
state lies right of b (`maxwell_right`). -/
theorem srk_omega1_unique_r5 : dropped% Checked.Chemistry.SRKAcentric.srk_omega1_unique 5 := by
  intro R ac b Tc vc vl vg ps hac hb hvc hc h
  have hRT := (crit_RT_pos R ac b 1 0 Tc vc hac hb hvc (Or.inl ⟨rfl, rfl⟩) hc).1
  have hθ := (Checked.Chemistry.SRKExists.theta_bounds R ac b Tc vc hac hb hvc hc).2
  have e : (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2 : ℝ) = 939 / 500 := by norm_num
  have h' := h
  rw [e] at h'
  have hα : 0 < 1 + 939 / 500 * (1 - Real.sqrt (7 / 10)) := by
    nlinarith [sqrt07_lt]
  have ha' : 0 < ac * (1 + 939 / 500 * (1 - Real.sqrt (7 / 10))) ^ 2 := by positivity
  have hcb : R * (7 / 10 * Tc) * b < ac * (1 + 939 / 500 * (1 - Real.sqrt (7 / 10))) ^ 2 := by
    have := (div_le_iff₀ ha').1 hθ
    nlinarith
  have hl := maxwell_right R (7 / 10 * Tc) _ b vl vg ps ha' hb (by nlinarith) hcb h'
  exact Checked.Chemistry.SRKAcentric.srk_omega1_unique R ac b Tc vc vl vg ps hac hb hvc hc hl h

/-- RK: `b < v_l` (hypothesis 7) is redundant (θ ≤ 0.1188 < 1 by `RKExists.theta_bounds`). -/
theorem rk_coexistence_unique_r7 : dropped% Checked.Chemistry.RKAcentric.rk_coexistence_unique 7 := by
  intro R A b Tc vc vl vg ps hR hA hb hTc hvc hc h
  have hθ := (Checked.Chemistry.RKExists.theta_bounds R A b Tc vc hR hA hb hTc hvc hc).2
  have ha' : 0 < A / Real.sqrt (7 / 10 * Tc) := div_pos hA (Real.sqrt_pos.2 (by positivity))
  have hcb : R * (7 / 10 * Tc) * b < A / Real.sqrt (7 / 10 * Tc) := by
    have := (div_le_iff₀ ha').1 hθ
    nlinarith
  have hl := maxwell_right R (7 / 10 * Tc) _ b vl vg ps ha' hb (by positivity) hcb h
  exact Checked.Chemistry.RKAcentric.rk_coexistence_unique R A b Tc vc vl vg ps hR hA hb hTc hvc hc hl h

end Checked.Trust.MaxwellRight
