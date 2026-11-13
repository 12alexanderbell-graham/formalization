import Checked.Trust.NonVacuity
import Checked.Chemistry.Coexistence
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# Maxwell coexistence states of the van der Waals isotherm lie right of the co-volume
(run 2026-11-13T0828Z)

For the van der Waals isotherm p(v) = c/(v − b) − a/v² (`cubicP R a b 0 0 T`, c = R T) with a > 0:

* if b > 0 and c > 0, every Maxwell coexistence state (v_l < v_g, p(v_l) = p(v_g) = p_s,
  ∫ p = p_s (v_g − v_l)) has v_l > b (`maxwell_right`);
* if b < 0 and c < 0, no Maxwell coexistence state has v_l > b (`no_maxwell_neg`);
* if b = 0 and c = 0, no Maxwell coexistence state has v_l > 0 (`no_maxwell_zero`).

So in `Checked.Chemistry.Coexistence.vdW_coexistence_unique` (temperature 0.7 · 8a/(27Rb), hence
c = 0.7 · 8a/(27b) has the sign of b) both `0 < b` (hypothesis 3) and `b < v_l` (hypothesis 4) are
redundant, each in the presence of the other hypotheses.

Proof: on an interval avoiding the poles b and 0 where c (v − b) < 0, p'' = 2c/(v − b)³ − 6a/v⁴ < 0,
so p is strictly concave and a strictly concave function equal to p_s at both ends has integral
above p_s (v_g − v_l). If the interval contains a pole, p is not integrable there (Lean's integral is
0), so p_s = 0; but p(v) < 0 wherever c (v − b) < 0 (Lean's a/0 = 0 included) and p(b) = −a/b² < 0.
-/

open Set Filter Topology MeasureTheory

namespace Checked.Trust.MaxwellRightVdW
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence

/-- A strictly concave function equal to `ps` at both ends of `[x, y]` has integral above
`ps (y − x)` (same statement as `Checked.Trust.MaxwellRight.integral_gt_of_strictConcave`). -/
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

/-- The van der Waals isotherm as `cubicP` with u = w = 0. -/
theorem cubicP_vdw (R T a b v : ℝ) :
    cubicP R a b 0 0 T v = R * T / (v - b) - a / v ^ 2 := by
  simp [cubicP]

section VdW
variable (c a b : ℝ)

/-- First derivative of c/(v − b) − a/v². -/
noncomputable def q1 (v : ℝ) : ℝ := -c / (v - b) ^ 2 + 2 * a / v ^ 3

/-- Second derivative of c/(v − b) − a/v². -/
noncomputable def q2 (v : ℝ) : ℝ := 2 * c / (v - b) ^ 3 - 6 * a / v ^ 4

theorem hasDerivAt_p (R T v : ℝ) (hv : v - b ≠ 0) (h0 : v ≠ 0) :
    HasDerivAt (cubicP R a b 0 0 T) (q1 (R * T) a b v) v := by
  have h1 : HasDerivAt (fun x => x - b) 1 v := (hasDerivAt_id v).sub_const b
  have hA := (hasDerivAt_const v (R * T)).div h1 hv
  have hB := (hasDerivAt_const v a).div (hasDerivAt_pow 2 v) (pow_ne_zero 2 h0)
  have := hA.sub hB
  have hfun : cubicP R a b 0 0 T = fun x => (fun _ => R * T) x / (fun x => x - b) x -
      (fun _ => a) x / (fun x => x ^ 2) x := by
    funext x; simp [cubicP]
  rw [hfun]
  convert this using 1
  unfold q1
  field_simp
  ring

theorem hasDerivAt_q1 {v : ℝ} (hv : v - b ≠ 0) (h0 : v ≠ 0) :
    HasDerivAt (q1 c a b) (q2 c a b v) v := by
  have h1 : HasDerivAt (fun x => x - b) 1 v := (hasDerivAt_id v).sub_const b
  have hA := (hasDerivAt_const v (-c)).div (h1.pow 2) (pow_ne_zero 2 hv)
  have hB := (hasDerivAt_const v (2 * a)).div (hasDerivAt_pow 3 v) (pow_ne_zero 3 h0)
  have := hA.add hB
  have hfun : q1 c a b = fun x => (fun _ => -c) x / ((fun x => x - b) x) ^ 2 +
      (fun _ => 2 * a) x / (fun x => x ^ 3) x := by
    funext x; simp [q1]
  rw [hfun]
  convert this using 1
  unfold q2
  simp only [Pi.pow_apply]
  field_simp
  ring

end VdW

/-- On an open set avoiding the poles, the second derivative of the vdW isotherm is `q2`. -/
theorem deriv2_eq (R T a b : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hUp : ∀ v ∈ U, v - b ≠ 0 ∧ v ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv^[2] (cubicP R a b 0 0 T) x = q2 (R * T) a b x := by
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
  have heq : deriv (cubicP R a b 0 0 T) =ᶠ[𝓝 x] q1 (R * T) a b := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hasDerivAt_p a b R T y (hUp y hy).1 (hUp y hy).2).deriv
  rw [heq.deriv_eq]
  exact (hasDerivAt_q1 (R * T) a b (hUp x hx).1 (hUp x hx).2).deriv

/-- Where `c (v − b) < 0`, the isotherm is negative (also at v = 0, where Lean's `a/0 = 0`). -/
theorem p_neg (R T a b v : ℝ) (ha : 0 < a) (hv : R * T * (v - b) < 0) :
    cubicP R a b 0 0 T v < 0 := by
  rw [cubicP_vdw]
  have hvb : v - b ≠ 0 := by intro h; rw [h, mul_zero] at hv; exact lt_irrefl 0 hv
  have h1 : R * T / (v - b) < 0 := by
    have e : R * T / (v - b) = R * T * (v - b) / (v - b) ^ 2 := by field_simp
    rw [e]; exact div_neg_of_neg_of_pos hv (by positivity)
  have h2 : 0 ≤ a / v ^ 2 := div_nonneg ha.le (sq_nonneg v)
  linarith

/-- At the co-volume itself the isotherm takes the junk value −a/b² < 0. -/
theorem p_at_b (R T a b : ℝ) (ha : 0 < a) (hb : b ≠ 0) : cubicP R a b 0 0 T b < 0 := by
  rw [cubicP_vdw, sub_self, div_zero, zero_sub, neg_neg_iff_pos]
  exact div_pos ha (by positivity)

/-- On a closed interval where `c (v − b) < 0` and `v ≠ 0`, the isotherm is continuous. -/
theorem cont_piece (R T a b x y : ℝ) (hS : ∀ v ∈ Icc x y, R * T * (v - b) < 0 ∧ v ≠ 0) :
    ContinuousOn (cubicP R a b 0 0 T) (Icc x y) := fun v hv => by
  have hvb : v - b ≠ 0 := fun h => by have := (hS v hv).1; rw [h, mul_zero] at this; exact lt_irrefl 0 this
  exact (hasDerivAt_p a b R T v hvb (hS v hv).2).continuousAt.continuousWithinAt

/-- On a closed interval where `c (v − b) < 0` and `v ≠ 0`, the isotherm is strictly concave. -/
theorem concave_piece (R T a b x y : ℝ) (ha : 0 < a)
    (hS : ∀ v ∈ Icc x y, R * T * (v - b) < 0 ∧ v ≠ 0) :
    StrictConcaveOn ℝ (Icc x y) (cubicP R a b 0 0 T) := by
  set U : Set ℝ := {v | R * T * (v - b) < 0} ∩ {v | v ≠ 0} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt (by fun_prop) continuous_const).inter isOpen_ne
  have hUp : ∀ v ∈ U, v - b ≠ 0 ∧ v ≠ 0 := fun v hv =>
    ⟨fun h => by have := hv.1; simp only [mem_ofPred_eq, h, mul_zero, lt_irrefl] at this, hv.2⟩
  have hsub : Icc x y ⊆ U := fun v hv => hS v hv
  have hcont : ContinuousOn (cubicP R a b 0 0 T) (Icc x y) := fun v hv =>
    (hasDerivAt_p a b R T v (hUp v (hsub hv)).1 (hUp v (hsub hv)).2).continuousAt.continuousWithinAt
  refine strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hcont (fun z hz => ?_)
  rw [interior_Icc] at hz
  have hzU : z ∈ U := hsub (Ioo_subset_Icc_self hz)
  rw [deriv2_eq R T a b hUo hUp hzU]
  unfold q2
  have hz0 : z ≠ 0 := hzU.2
  have hzb : z - b ≠ 0 := (hUp z hzU).1
  have hneg : R * T * (z - b) < 0 := hzU.1
  have e : 2 * (R * T) / (z - b) ^ 3 = 2 * (R * T * (z - b)) / (z - b) ^ 4 := by
    field_simp
  have h1 : 2 * (R * T) / (z - b) ^ 3 < 0 := by
    rw [e]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2 : 0 < 6 * a / z ^ 4 := div_pos (by linarith) (by positivity)
  linarith

/-- If `c ≠ 0`, `a ≠ 0`, the isotherm is not integrable on an interval `[x, y]` containing exactly one
of the poles `b`, `0`. -/
theorem not_ii (R T a b x y : ℝ) (hc : R * T ≠ 0) (ha : a ≠ 0) (hxy : x < y)
    (hp : (b ∈ Icc x y ∧ (0 : ℝ) ∉ Icc x y) ∨ ((0 : ℝ) ∈ Icc x y ∧ b ∉ Icc x y)) :
    ¬ IntervalIntegrable (cubicP R a b 0 0 T) volume x y := by
  intro hi
  have hu : uIcc x y = Icc x y := uIcc_of_le hxy.le
  rcases hp with ⟨hb, h0⟩ | ⟨h0, hb⟩
  · -- pole at b: subtract the continuous −a/v² part
    have hcont : ContinuousOn (fun v : ℝ => a / v ^ 2) (uIcc x y) := by
      rw [hu]
      exact continuousOn_const.div (continuousOn_pow 2) (fun v hv => pow_ne_zero 2
        (fun h => h0 (h ▸ hv)))
    have h2 := hi.add (hcont.intervalIntegrable (μ := volume))
    have h3 := h2.const_mul (R * T)⁻¹
    have h4 : IntervalIntegrable (fun v => (v - b)⁻¹) volume x y := by
      refine h3.congr fun v _ => ?_
      simp only [cubicP_vdw]
      rw [sub_add_cancel, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [intervalIntegrable_sub_inv_iff] at h4
    rcases h4 with h | h
    · exact hxy.ne h
    · exact h (by rw [hu]; exact hb)
  · -- pole at 0: multiply by v and subtract the continuous v c/(v − b) part
    have hcont1 : ContinuousOn (fun v : ℝ => v) (uIcc x y) := continuousOn_id
    have h1 := hi.continuousOn_mul hcont1
    have hcont2 : ContinuousOn (fun v : ℝ => v * (R * T / (v - b))) (uIcc x y) := by
      rw [hu]
      refine continuousOn_id.mul (continuousOn_const.div (continuousOn_id.sub continuousOn_const)
        (fun v hv h => hb ?_))
      have : v = b := by simpa [sub_eq_zero] using h
      exact this ▸ hv
    have h2 := (h1.sub (hcont2.intervalIntegrable (μ := volume))).const_mul (-a⁻¹)
    have h4 : IntervalIntegrable (fun v : ℝ => v⁻¹) volume x y := by
      refine h2.congr fun v _ => ?_
      simp only [cubicP_vdw]
      rcases eq_or_ne v 0 with h | h
      · rw [h]; simp
      · field_simp; ring
    rw [intervalIntegrable_inv_iff] at h4
    rcases h4 with h | h
    · exact hxy.ne h
    · exact h (by rw [hu]; exact h0)

/-- **Every Maxwell coexistence state of the van der Waals isotherm with b > 0 and c = R T > 0 lies
right of the co-volume.** -/
theorem maxwell_right (R T a b vl vg ps : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < R * T)
    (h : IsMaxwellCoexistence (cubicP R a b 0 0 T) vl vg ps) : b < vl := by
  by_contra hvl
  have hvl : vl ≤ b := not_lt.1 hvl
  obtain ⟨hlg, hpl, hpg, hint⟩ := h
  have nz : cubicP R a b 0 0 T vl ≠ 0 := by
    rcases eq_or_lt_of_le hvl with e | e
    · rw [e]; exact (p_at_b R T a b ha hb.ne').ne
    · exact (p_neg R T a b vl ha (mul_neg_of_pos_of_neg hc (by linarith))).ne
  by_cases hpole : b ∈ Icc vl vg ∨ (0 : ℝ) ∈ Icc vl vg
  · have hni : ¬ IntervalIntegrable (cubicP R a b 0 0 T) volume vl vg := by
      by_cases hb' : b ∈ Icc vl vg
      · by_cases h0 : (0 : ℝ) ∈ Icc vl vg
        · -- both poles: restrict to [max vl (b/2), vg], which contains b and not 0
          intro hi
          set x' := max vl (b / 2) with hx'
          have hx'b : x' ≤ b := max_le hvl (by linarith)
          have hx'g : x' < vg := max_lt hlg (by linarith [hb'.2])
          have hsub : uIcc x' vg ⊆ uIcc vl vg := by
            rw [uIcc_of_le hx'g.le, uIcc_of_le hlg.le]
            exact Icc_subset_Icc (le_max_left _ _) le_rfl
          have hi' := hi.mono_set hsub
          exact not_ii R T a b x' vg hc.ne' ha.ne' hx'g
            (Or.inl ⟨⟨hx'b, hb'.2⟩, fun h => by
              have : b / 2 ≤ x' := le_max_right _ _
              linarith [h.1]⟩) hi'
        · exact not_ii R T a b vl vg hc.ne' ha.ne' hlg (Or.inl ⟨hb', h0⟩)
      · exact not_ii R T a b vl vg hc.ne' ha.ne' hlg (Or.inr ⟨hpole.resolve_left hb', hb'⟩)
    rw [intervalIntegral.integral_undef hni] at hint
    have hps : ps = 0 := by
      rcases mul_eq_zero.1 hint.symm with h | h
      · exact h
      · exact absurd h (by linarith)
    exact nz (hpl.trans hps)
  · simp only [not_or, mem_Icc, not_and, not_le] at hpole
    obtain ⟨hpb, hp0⟩ := hpole
    have hvg : vg < b := hpb hvl
    have hS : ∀ v ∈ Icc vl vg, R * T * (v - b) < 0 ∧ v ≠ 0 := by
      intro v hv
      refine ⟨mul_neg_of_pos_of_neg hc (by linarith [hv.2]), ?_⟩
      rintro rfl
      rcases le_or_gt vl 0 with h | h
      · exact absurd (hp0 h) (by linarith [hv.2])
      · linarith [hv.1]
    have := integral_gt_of_strictConcave hlg
      (cont_piece R T a b vl vg hS)
      (concave_piece R T a b vl vg ha hS) hpl hpg
    linarith

/-- For c = R T < 0 (the case b < 0 below) no Maxwell coexistence state of the vdW isotherm has v_l > b. -/
theorem no_maxwell_neg (R T a b vl vg ps : ℝ) (ha : 0 < a) (hc : R * T < 0)
    (hl : b < vl) (h : IsMaxwellCoexistence (cubicP R a b 0 0 T) vl vg ps) : False := by
  obtain ⟨hlg, hpl, hpg, hint⟩ := h
  have nz : cubicP R a b 0 0 T vl ≠ 0 :=
    (p_neg R T a b vl ha (mul_neg_of_neg_of_pos hc (by linarith))).ne
  have hbI : b ∉ Icc vl vg := fun h => by linarith [h.1]
  by_cases h0 : (0 : ℝ) ∈ Icc vl vg
  · have hni := not_ii R T a b vl vg hc.ne ha.ne' hlg (Or.inr ⟨h0, hbI⟩)
    rw [intervalIntegral.integral_undef hni] at hint
    have hps : ps = 0 := by
      rcases mul_eq_zero.1 hint.symm with h | h
      · exact h
      · exact absurd h (by linarith)
    exact nz (hpl.trans hps)
  · have hS : ∀ v ∈ Icc vl vg, R * T * (v - b) < 0 ∧ v ≠ 0 := by
      intro v hv
      refine ⟨mul_neg_of_neg_of_pos hc (by linarith [hv.1]), ?_⟩
      rintro rfl
      exact h0 hv
    have := integral_gt_of_strictConcave hlg
      (cont_piece R T a b vl vg hS)
      (concave_piece R T a b vl vg ha hS) hpl hpg
    linarith

/-- For b = 0 at temperature 0 the vdW isotherm is −a/v², strictly increasing for v > 0: no Maxwell
coexistence state has v_l > 0. -/
theorem no_maxwell_zero (R a vl vg ps : ℝ) (ha : 0 < a) (hl : 0 < vl)
    (h : IsMaxwellCoexistence (cubicP R a 0 0 0 0) vl vg ps) : False := by
  obtain ⟨hlg, hpl, hpg, -⟩ := h
  rw [cubicP_vdw] at hpl hpg
  have hvg : 0 < vg := by linarith
  have e : a / vl ^ 2 = a / vg ^ 2 := by simp at hpl hpg; linarith
  rw [div_eq_div_iff (by positivity) (by positivity)] at e
  have : vg ^ 2 = vl ^ 2 := mul_left_cancel₀ ha.ne' e
  nlinarith

/-! ## The hypotheses `0 < b` and `b < v_l` of `vdW_coexistence_unique` are redundant -/

/-- `0 < b` (hypothesis 3) is redundant: for b < 0 the temperature 0.7 · 8a/(27Rb) makes R T < 0 and
no Maxwell state has v_l > b (`no_maxwell_neg`); for b = 0 Lean's x/0 = 0 gives temperature 0 and
the isotherm −a/v² has no Maxwell state with v_l > 0 (`no_maxwell_zero`). -/
theorem vdW_coexistence_unique_r3 :
    dropped% Checked.Chemistry.Coexistence.vdW_coexistence_unique 3 := by
  intro R a b vl vg ps hR ha hl h
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · exfalso
    have hc : R * (7 / 10 * (8 * a / (27 * R * b))) < 0 := by
      have e : R * (7 / 10 * (8 * a / (27 * R * b))) = 7 / 10 * (8 * a / (27 * b)) := by
        field_simp
      rw [e]
      exact mul_neg_of_pos_of_neg (by norm_num) (div_neg_of_pos_of_neg (by linarith) (by linarith))
    exact no_maxwell_neg R _ a b vl vg ps ha hc hl h
  · exfalso
    have e : (7 / 10 * (8 * a / (27 * R * 0)) : ℝ) = 0 := by simp
    rw [e] at h
    exact no_maxwell_zero R a vl vg ps ha hl h
  · exact Checked.Chemistry.Coexistence.vdW_coexistence_unique R a b vl vg ps hR ha hb hl h

/-- `b < v_l` (hypothesis 4) is redundant: R T = 0.7 · 8a/(27b) > 0, so every Maxwell state lies
right of b (`maxwell_right`). -/
theorem vdW_coexistence_unique_r4 :
    dropped% Checked.Chemistry.Coexistence.vdW_coexistence_unique 4 := by
  intro R a b vl vg ps hR ha hb h
  have hc : 0 < R * (7 / 10 * (8 * a / (27 * R * b))) := by positivity
  exact Checked.Chemistry.Coexistence.vdW_coexistence_unique R a b vl vg ps hR ha hb
    (maxwell_right R _ a b vl vg ps ha hb hc h) h

end Checked.Trust.MaxwellRightVdW
