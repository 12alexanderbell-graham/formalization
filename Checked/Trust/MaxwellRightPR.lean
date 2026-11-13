import Checked.Trust.MaxwellRight
import Checked.Chemistry.PRExists
import Checked.Chemistry.PR78Exists
import Checked.Chemistry.PRAcentric
import Checked.Chemistry.PR78Acentric

/-!
# Maxwell coexistence states of a cold Peng–Robinson isotherm lie right of the co-volume
(run 2026-11-13T0828Z)

For the Peng–Robinson isotherm p(v) = c/(v − b) − a/D(v), D(v) = v² + 2bv − b²
(`cubicP R a b 2 (-1) T`, c = R T) with a > 0, b > 0, c > 0 and reduced temperature c b/a at most one tenth,
every Maxwell coexistence state (v_l < v_g, p(v_l) = p(v_g) = p_s, ∫ p = p_s (v_g − v_l)) has
v_l > b (`maxwell_right_pr`). So the hypothesis `b < v_l` of the PR (1976) and PR (1978)
acentric-factor uniqueness theorems is redundant: at their coexistence temperature the reduced
temperature is below one tenth (`PRExists.theta_bounds`, `PR78Exists.theta_bounds`).

Proof. Left of b the isotherm has three poles: b and the two zeros of D. If [v_l, v_g] contains one,
p is not integrable there and Lean's integral is 0, so p_s = 0; but p has no zero at or left of b:
where D ≥ 0 both terms are ≤ 0 and one is < 0 (Lean's a/0 = 0 included), and where D < 0 one has
v < 4b/5 and |D| ≤ 2b², so a(b − v) > ab/5 ≥ c|D|. Otherwise D has one sign on the interval: where
D > 0 the second derivative 2c/(v − b)³ − a(6(v + b)² + 4b²)/D³ is negative (strictly concave), where
D < 0 it is positive (strictly convex: (6u² + 4b²)(2b − u)³ > 2b⁵ for u = v + b with u² < 2b², while
2c|D|³ ≤ 8ab⁵/5); a strictly concave (convex) function equal to p_s at both ends has integral above
(below) p_s (v_g − v_l).
-/

open Set Filter Topology MeasureTheory

namespace Checked.Trust.MaxwellRightPR
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence Checked.Trust.NecessityO
open Checked.Trust.MaxwellRight

/-- The PR denominator. -/
theorem prD (b v : ℝ) : v ^ 2 + 2 * b * v + (-1) * b ^ 2 = (v + b) ^ 2 - 2 * b ^ 2 := by ring

/-- The second derivative of the PR isotherm away from its poles. -/
theorem deriv2_pr (R T a b v : ℝ) (hv : v - b ≠ 0) (hD : v ^ 2 + 2 * b * v + (-1) * b ^ 2 ≠ 0) :
    deriv^[2] (cubicP R a b 2 (-1) T) v = 2 * (R * T) / (v - b) ^ 3 -
      a * (6 * (v + b) ^ 2 + 4 * b ^ 2) / (v ^ 2 + 2 * b * v + (-1) * b ^ 2) ^ 3 := by
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, deriv2_P R a b 2 (-1) T v hv hD]
  have e : 2 * a * ((v ^ 2 + 2 * b * v + -1 * b ^ 2) - (2 * v + 2 * b) ^ 2) =
      -(a * (6 * (v + b) ^ 2 + 4 * b ^ 2)) := by ring
  rw [e, neg_div, ← sub_eq_add_neg, mul_assoc]

/-- Where D < 0: v < 4b/5 and |D| ≤ 2b². -/
theorem dneg_facts (b v : ℝ) (hb : 0 < b) (hD : v ^ 2 + 2 * b * v + (-1) * b ^ 2 < 0) :
    v < 4 / 5 * b ∧ -(v ^ 2 + 2 * b * v + (-1) * b ^ 2) ≤ 2 * b ^ 2 := by
  rw [prD] at hD ⊢
  constructor
  · by_contra h; push Not at h; nlinarith
  · nlinarith [sq_nonneg (v + b)]

/-- The cold PR isotherm has no zero at or left of b (junk values at the poles included). -/
theorem p_ne_zero (R T a b v : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < R * T)
    (hθ : R * T * b ≤ a / 10) (hv : v ≤ b) : cubicP R a b 2 (-1) T v ≠ 0 := by
  unfold cubicP
  rcases eq_or_lt_of_le hv with rfl | hv
  · rw [sub_self, div_zero, zero_sub, neg_ne_zero]
    exact div_ne_zero ha.ne' (by nlinarith)
  set D := v ^ 2 + 2 * b * v + (-1) * b ^ 2 with hDdef
  have h1 : R * T / (v - b) < 0 := div_neg_of_pos_of_neg hc (by linarith)
  rcases lt_trichotomy D 0 with hD | hD | hD
  · obtain ⟨hv4, hDb⟩ := dneg_facts b v hb hD
    intro h
    rw [sub_eq_zero, div_eq_div_iff (by linarith) hD.ne] at h
    -- R T D = a (v − b), with R T |D| ≤ (a/(10 b)) 2b² < a (b − v)
    have : R * T * (-D) ≤ R * T * (2 * b ^ 2) := mul_le_mul_of_nonneg_left hDb hc.le
    nlinarith
  · rw [hD, div_zero, sub_zero]; exact h1.ne
  · have : 0 < a / D := div_pos ha hD
    intro h; linarith

/-- On a closed interval left of b with no zero of D, the cold PR isotherm is strictly concave
(D > 0) or strictly convex (D < 0), and continuous. -/
theorem cont_piece (R T a b x y : ℝ)
    (hS : ∀ v ∈ Icc x y, v - b ≠ 0 ∧ v ^ 2 + 2 * b * v + (-1) * b ^ 2 ≠ 0) :
    ContinuousOn (cubicP R a b 2 (-1) T) (Icc x y) := fun v hv =>
  (hasDerivAt_P R a b 2 (-1) T v (hS v hv).1 (hS v hv).2).continuousAt.continuousWithinAt

theorem p2_neg (R T a b v : ℝ) (ha : 0 < a) (hc : 0 < R * T) (hv : v < b)
    (hD : 0 < v ^ 2 + 2 * b * v + (-1) * b ^ 2) :
    2 * (R * T) / (v - b) ^ 3 - a * (6 * (v + b) ^ 2 + 4 * b ^ 2) / (v ^ 2 + 2 * b * v + (-1) * b ^ 2) ^ 3 < 0 := by
  have h1 : 2 * (R * T) / (v - b) ^ 3 < 0 :=
    div_neg_of_pos_of_neg (by linarith) (Odd.pow_neg (by decide) (by linarith))
  have h2 : 0 < a * (6 * (v + b) ^ 2 + 4 * b ^ 2) / (v ^ 2 + 2 * b * v + (-1) * b ^ 2) ^ 3 := by
    apply div_pos _ (pow_pos hD 3)
    have h6 : 0 < 6 * (v + b) ^ 2 + 4 * b ^ 2 := by
      have : 0 < (v + b) ^ 2 := by rw [prD] at hD; nlinarith [sq_nonneg b]
      nlinarith [sq_nonneg b]
    exact mul_pos ha h6
  linarith

/-- The polynomial inequality behind convexity where D < 0. -/
theorem poly_bound (b u : ℝ) (hb : 0 < b) (hu : u ^ 2 < 2 * b ^ 2) :
    2 * b ^ 5 < (6 * u ^ 2 + 4 * b ^ 2) * (2 * b - u) ^ 3 := by
  have hu1 : u < 283 / 200 * b := by nlinarith
  rcases le_or_gt u b with h | h
  · have h1 : b ≤ 2 * b - u := by linarith
    have h3 : b ^ 3 ≤ (2 * b - u) ^ 3 := pow_le_pow_left₀ hb.le h1 3
    have h4 : 4 * b ^ 2 ≤ 6 * u ^ 2 + 4 * b ^ 2 := by nlinarith [sq_nonneg u]
    have hb5 : 0 < b ^ 5 := by positivity
    have : 4 * b ^ 2 * b ^ 3 ≤ (6 * u ^ 2 + 4 * b ^ 2) * (2 * b - u) ^ 3 :=
      mul_le_mul h4 h3 (by positivity) (by nlinarith [sq_nonneg u])
    nlinarith
  · have h1 : 117 / 200 * b ≤ 2 * b - u := by linarith
    have h3 : (117 / 200 * b) ^ 3 ≤ (2 * b - u) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
    have h4 : 10 * b ^ 2 ≤ 6 * u ^ 2 + 4 * b ^ 2 := by nlinarith
    have : 10 * b ^ 2 * (117 / 200 * b) ^ 3 ≤ (6 * u ^ 2 + 4 * b ^ 2) * (2 * b - u) ^ 3 :=
      mul_le_mul h4 h3 (by positivity) (by nlinarith [sq_nonneg u])
    have hb5 : 0 < b ^ 5 := by positivity
    nlinarith

theorem p2_pos (R T a b v : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < R * T) (hθ : R * T * b ≤ a / 10)
    (hD : v ^ 2 + 2 * b * v + (-1) * b ^ 2 < 0) :
    0 < 2 * (R * T) / (v - b) ^ 3 - a * (6 * (v + b) ^ 2 + 4 * b ^ 2) / (v ^ 2 + 2 * b * v + (-1) * b ^ 2) ^ 3 := by
  obtain ⟨hv4, hDb⟩ := dneg_facts b v hb hD
  set D := v ^ 2 + 2 * b * v + (-1) * b ^ 2 with hDdef
  set E := -D with hE
  have hE0 : 0 < E := by rw [hE]; linarith
  set r := b - v with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hu : (v + b) ^ 2 < 2 * b ^ 2 := by have := hD; rw [hDdef, prD] at this; linarith
  have hpoly := poly_bound b (v + b) hb hu
  have e1 : 2 * (R * T) / (v - b) ^ 3 = -(2 * (R * T) / r ^ 3) := by
    rw [show v - b = -r by rw [hr]; ring, neg_pow, show ((-1 : ℝ)) ^ 3 = -1 by norm_num, neg_one_mul,
      div_neg]
  have e2 : a * (6 * (v + b) ^ 2 + 4 * b ^ 2) / D ^ 3 = -(a * (6 * (v + b) ^ 2 + 4 * b ^ 2) / E ^ 3) := by
    rw [show D = -E by rw [hE]; ring, neg_pow, show ((-1 : ℝ)) ^ 3 = -1 by norm_num, neg_one_mul, div_neg]
  rw [e1, e2, sub_neg_eq_add, neg_add_eq_sub, sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
  -- 2c E³ ≤ 2 (a/(10b)) (2b²)³ = (8/5) a b⁵ < 2 a b⁵ < a (6u² + 4b²) r³
  have hE3 : E ^ 3 ≤ (2 * b ^ 2) ^ 3 := pow_le_pow_left₀ hE0.le hDb 3
  have hr3 : 2 * b - (v + b) = r := by rw [hr]; ring
  rw [hr3] at hpoly
  have k1 : 2 * (R * T) * E ^ 3 ≤ 2 * (R * T) * (2 * b ^ 2) ^ 3 :=
    mul_le_mul_of_nonneg_left hE3 (by linarith)
  have k2 : 2 * (R * T) * (2 * b ^ 2) ^ 3 * b ≤ 2 * (a / 10) * (2 * b ^ 2) ^ 3 := by
    have : 0 ≤ 2 * (2 * b ^ 2) ^ 3 := by positivity
    nlinarith
  have k3 : a * (2 * b ^ 5) < a * ((6 * (v + b) ^ 2 + 4 * b ^ 2) * r ^ 3) := mul_lt_mul_of_pos_left hpoly ha
  have hb' : 0 < b := hb
  nlinarith [pow_pos hb 5, pow_pos hb 6]

/-- Where D has no zero on a closed interval, it keeps the sign it has at the left end. -/
theorem D_sign (b x y : ℝ) (hxy : x ≤ y) (hS : ∀ v ∈ Icc x y, v ^ 2 + 2 * b * v + (-1) * b ^ 2 ≠ 0) :
    (∀ v ∈ Icc x y, 0 < v ^ 2 + 2 * b * v + (-1) * b ^ 2) ∨
      (∀ v ∈ Icc x y, v ^ 2 + 2 * b * v + (-1) * b ^ 2 < 0) := by
  have hcont : Continuous (fun v : ℝ => v ^ 2 + 2 * b * v + (-1) * b ^ 2) := by fun_prop
  rcases lt_or_gt_of_ne (hS x (left_mem_Icc.2 hxy)) with h0 | h0
  · right
    intro v hv
    by_contra hpos; push Not at hpos
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hv.1 hcont.continuousOn ⟨h0.le, hpos⟩
    exact hS z ⟨hz.1, hz.2.trans hv.2⟩ hz0
  · left
    intro v hv
    by_contra hneg; push Not at hneg
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hv.1 hcont.continuousOn ⟨hneg, h0.le⟩
    exact hS z ⟨hz.1, hz.2.trans hv.2⟩ hz0

/-- **Every Maxwell coexistence state of a cold PR isotherm (R T b ≤ a/10) lies right of b.** -/
theorem maxwell_right_pr (R T a b vl vg ps : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < R * T)
    (hθ : R * T * b ≤ a / 10) (h : IsMaxwellCoexistence (cubicP R a b 2 (-1) T) vl vg ps) : b < vl := by
  by_contra hvl
  have hvl : vl ≤ b := not_lt.1 hvl
  obtain ⟨hlg, hpl, hpg, hint⟩ := h
  have nz := p_ne_zero R T a b vl ha hb hc hθ hvl
  have hu : ∀ z, z ∈ Icc vl vg → z ∈ uIcc vl vg := fun z hz => by rw [uIcc_of_le hlg.le]; exact hz
  by_cases hpole : b ∈ Icc vl vg ∨ ∃ z ∈ Icc vl vg, z ^ 2 + 2 * b * z + (-1) * b ^ 2 = 0
  · have hni : ¬ IntervalIntegrable (cubicP R a b 2 (-1) T) volume vl vg := by
      rcases hpole with hp | ⟨z, hz, hz0⟩
      · refine not_ii_of_pole _ (fun x => -a / (x ^ 2 + 2 * b * x + (-1) * b ^ 2)) (fun _ => 1) b (R * T)
          hc.ne' continuousAt_const one_ne_zero
          (continuousAt_const.div (by fun_prop) (by nlinarith))
          (Eventually.of_forall fun x => by unfold cubicP; ring) hlg.ne (hu _ hp)
      · -- D(x) = (x − z)(x + 2b + z)
        have hzb : z - b ≠ 0 := by
          intro e
          have hzb' : z = b := by linarith
          rw [hzb'] at hz0; nlinarith
        have hm : z + 2 * b + z ≠ 0 := by
          intro e
          have hzb' : z = -b := by linarith
          rw [hzb'] at hz0; nlinarith
        refine not_ii_of_pole _ (fun x => R * T / (x - b)) (fun x => x + 2 * b + z) z (-a)
          (neg_ne_zero.2 ha.ne') (by fun_prop) hm
          (continuousAt_const.div (by fun_prop) hzb) ?_ hlg.ne (hu _ hz)
        refine Eventually.of_forall fun x => ?_
        have eD : x ^ 2 + 2 * b * x + (-1) * b ^ 2 = (x - z) * (x + 2 * b + z) := by
          linear_combination hz0
        unfold cubicP
        rw [eD]; ring
    rw [intervalIntegral.integral_undef hni] at hint
    have hps : ps = 0 := by
      rcases mul_eq_zero.1 hint.symm with h | h
      · exact h
      · exact absurd h (by linarith)
    exact nz (hpl.trans hps)
  · simp only [not_or, not_exists, not_and] at hpole
    obtain ⟨hpb, hpD⟩ := hpole
    have hvg : vg < b := by
      by_contra h; push Not at h; exact hpb ⟨hvl, h⟩
    have hS : ∀ v ∈ Icc vl vg, v - b ≠ 0 ∧ v ^ 2 + 2 * b * v + (-1) * b ^ 2 ≠ 0 := fun v hv =>
      ⟨by linarith [hv.2], hpD v hv⟩
    have hcont := cont_piece R T a b vl vg hS
    rcases D_sign b vl vg hlg.le (fun v hv => (hS v hv).2) with hpos | hneg
    · have hcc : StrictConcaveOn ℝ (Icc vl vg) (cubicP R a b 2 (-1) T) :=
        strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hcont (fun x hx => by
          rw [interior_Icc] at hx
          have hx' := Ioo_subset_Icc_self hx
          rw [deriv2_pr R T a b x (hS x hx').1 (hS x hx').2]
          exact p2_neg R T a b x ha hc (by linarith [hx'.2]) (hpos x hx'))
      have := integral_gt_of_strictConcave hlg hcont hcc hpl hpg
      linarith
    · have hcc : StrictConvexOn ℝ (Icc vl vg) (cubicP R a b 2 (-1) T) :=
        strictConvexOn_of_deriv2_pos (convex_Icc _ _) hcont (fun x hx => by
          rw [interior_Icc] at hx
          have hx' := Ioo_subset_Icc_self hx
          rw [deriv2_pr R T a b x (hS x hx').1 (hS x hx').2]
          exact p2_pos R T a b x ha hb hc hθ (hneg x hx'))
      have := integral_lt_of_strictConvex hlg hcont hcc hpl hpg
      linarith

/-! ## The hypothesis `b < v_l` of the PR and PR78 uniqueness theorems is redundant -/

/-- PR (1976 κ) at ω = 1: `b < v_l` (hypothesis 5) is redundant. The critical point gives R T_c > 0
and the reduced coexistence temperature θ = R T b/a ≤ 0.074 < 1/10 (`PRExists.theta_bounds`), so every
Maxwell state lies right of b (`maxwell_right_pr`). -/
theorem pr_omega1_unique_r5 : dropped% Checked.Chemistry.PRAcentric.pr_omega1_unique 5 := by
  intro R ac b Tc vc vl vg ps hac hb hvc hc h
  have hRT := (crit_RT_pos R ac b 2 (-1) Tc vc hac hb hvc (Or.inr ⟨rfl, rfl⟩) hc).1
  have hθ := (Checked.Chemistry.PRExists.theta_bounds R ac b Tc vc hac hb hvc hc).2
  have e : (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2 : ℝ) = 82349 / 50000 := by norm_num
  have h' := h
  rw [e] at h'
  have hα : 0 < 1 + 82349 / 50000 * (1 - Real.sqrt (7 / 10)) := by nlinarith [sqrt07_lt]
  have ha' : 0 < ac * (1 + 82349 / 50000 * (1 - Real.sqrt (7 / 10))) ^ 2 := by positivity
  have hcb : R * (7 / 10 * Tc) * b ≤ ac * (1 + 82349 / 50000 * (1 - Real.sqrt (7 / 10))) ^ 2 / 10 := by
    have := (div_le_iff₀ ha').1 hθ
    nlinarith
  have hl := maxwell_right_pr R (7 / 10 * Tc) _ b vl vg ps ha' hb (by nlinarith) hcb h'
  exact Checked.Chemistry.PRAcentric.pr_omega1_unique R ac b Tc vc vl vg ps hac hb hvc hc hl h

/-- PR (1978 κ) at ω = 1: `b < v_l` (hypothesis 5) is redundant (θ ≤ 0.073 by
`PR78Exists.theta_bounds`). -/
theorem pr78_omega1_unique_r5 : dropped% Checked.Chemistry.PR78Acentric.pr78_omega1_unique 5 := by
  intro R ac b Tc vc vl vg ps hac hb hvc hc h
  have hRT := (crit_RT_pos R ac b 2 (-1) Tc vc hac hb hvc (Or.inr ⟨rfl, rfl⟩) hc).1
  have hθ := (Checked.Chemistry.PR78Exists.theta_bounds R ac b Tc vc hac hb hvc hc).2
  have e : (0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3 : ℝ) = 343383 / 200000 := by
    norm_num
  have h' := h
  rw [e] at h'
  have hα : 0 < 1 + 343383 / 200000 * (1 - Real.sqrt (7 / 10)) := by nlinarith [sqrt07_lt]
  have ha' : 0 < ac * (1 + 343383 / 200000 * (1 - Real.sqrt (7 / 10))) ^ 2 := by positivity
  have hcb : R * (7 / 10 * Tc) * b ≤ ac * (1 + 343383 / 200000 * (1 - Real.sqrt (7 / 10))) ^ 2 / 10 := by
    have := (div_le_iff₀ ha').1 hθ
    nlinarith
  have hl := maxwell_right_pr R (7 / 10 * Tc) _ b vl vg ps ha' hb (by nlinarith) hcb h'
  exact Checked.Chemistry.PR78Acentric.pr78_omega1_unique R ac b Tc vc vl vg ps hac hb hvc hc hl h

end Checked.Trust.MaxwellRightPR
