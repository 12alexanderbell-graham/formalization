import Mathlib
import Checked.Sim.ODETools
import Work.Sim.OneSided
import Work.Sim.RobCell

/-!
# Robertson network: the one-sided cell step with a weight chosen per cell

Same as `Work.Sim.RobCell.cell`/`step`, with the weighted norm d²·e₂² + e₃² for any d > 0
(`RobCell` fixes d = 70). At long horizons the weight that makes the network almost
non-expanding falls with y₂ (float study `runs/2026-11-06T0628Z/scripts/rob_feas_long.py`);
`weight_down` passes a bound to a smaller weight at no cost.
-/

namespace Work.Sim.RobCellD
open Set Checked.Sim Work.Sim.RobCell

variable {d : ℝ}

/-- Passing to a smaller weight costs nothing. -/
theorem weight_down {d d' e2 e3 R : ℝ} (hd' : 0 ≤ d') (hdd : d' ≤ d)
    (h : d ^ 2 * e2 ^ 2 + e3 ^ 2 ≤ R ^ 2) : d' ^ 2 * e2 ^ 2 + e3 ^ 2 ≤ R ^ 2 := by
  have : d' ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hd' hdd 2
  nlinarith [sq_nonneg e2]

/-- An affine function is bounded on [L, U] by the larger of its endpoint values. -/
theorem affine_bound {α β L U x Cm : ℝ} (hL : L ≤ x) (hU : x ≤ U)
    (h1 : |α + β * L| ≤ Cm) (h2 : |α + β * U| ≤ Cm) : |α + β * x| ≤ Cm := by
  rw [abs_le] at h1 h2 ⊢
  rcases le_total 0 β with hb | hb
  · have a := mul_le_mul_of_nonneg_left hL hb
    have b := mul_le_mul_of_nonneg_left hU hb
    constructor <;> linarith [h1.1, h2.2]
  · have a := mul_le_mul_of_nonpos_left hL hb
    have b := mul_le_mul_of_nonpos_left hU hb
    constructor <;> linarith [h1.2, h2.1]

/-- The affine coefficient C(x) of the one-sided form is bounded by its endpoint values. -/
theorem C_boundD {L U x Cm : ℝ} (hL : L ≤ x) (hU : x ≤ U)
    (h1 : |-(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * L + 2 * 30000000 * L| ≤ Cm)
    (h2 : |-(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * U + 2 * 30000000 * U| ≤ Cm) :
    |-(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * x + 2 * 30000000 * x| ≤ Cm := by
  have e : ∀ y : ℝ, -(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * y + 2 * 30000000 * y
      = -(d ^ 2 * (1 / 25)) + (2 * 30000000 - d ^ 2 * 10000) * y := fun y => by ring
  rw [e] at h1 h2 ⊢
  exact affine_bound hL hU h1 h2

/-- Weighted ball: componentwise bounds. -/
theorem ball_compD {h2 h3 B : ℝ} (hd : 0 < d) (hB : 0 ≤ B) (hh : d ^ 2 * h2 ^ 2 + h3 ^ 2 ≤ B ^ 2) :
    |h2| ≤ B / d ∧ |h3| ≤ B := by
  constructor
  · have : (d * h2) ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg h3]
    have h := abs_le_of_sq hB this
    rw [abs_mul, abs_of_pos hd] at h
    rw [le_div_iff₀ hd]; linarith
  · exact abs_le_of_sq hB (by nlinarith [sq_nonneg h2])

/-- Monotone bound R(t) ≤ R(b). -/
theorem R_leD {δ ε μ x h B : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hμ : 0 < μ) (hx0 : 0 ≤ x) (hxh : x ≤ h)
    (hμh : μ * h ≤ 1) (hBb : (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) ≤ B) :
    0 ≤ (δ + ε * x) * Real.exp (μ * x) ∧ (δ + ε * x) * Real.exp (μ * x) ≤ B := by
  have hpos : 0 ≤ δ + ε * x := by nlinarith
  refine ⟨mul_nonneg hpos (Real.exp_pos _).le, ?_⟩
  have h1 : δ + ε * x ≤ δ + ε * h := by nlinarith
  have hμx : μ * x ≤ μ * h := mul_le_mul_of_nonneg_left hxh hμ.le
  have hh0 : 0 ≤ h := hx0.trans hxh
  have h2 : Real.exp (μ * x) ≤ 1 + μ * h + (μ * h) ^ 2 :=
    (Real.exp_le_exp.2 hμx).trans (exp_le_quad (mul_nonneg hμ.le hh0) hμh)
  calc (δ + ε * x) * Real.exp (μ * x) ≤ (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith)
    _ ≤ B := hBb

theorem cellD (p2 p3 : List ℚ) (hd : 0 < d) {P Q : ℝ → ℝ → ℝ}
    (hP : ∀ y2 y3, -1 / 1000 ≤ y2 → y2 ≤ 1 / 1000 → -1 / 10 ≤ y3 → y3 ≤ 11 / 10 →
      P y2 y3 = robP y2 y3 ∧ Q y2 y3 = robQ y2 y3)
    {T t0 h Δ δ ε μ B A Cm L2 U2 L3 U3 e2 e3 c2 c3 : ℝ} {y2 y3 : ℝ → ℝ}
    (ht0 : 0 ≤ t0) (hT : t0 + h ≤ T) (hh : 0 < h)
    (hd2 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y2 (P (y2 t) (y3 t)) (Icc 0 T) t)
    (hd3 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y3 (Q (y2 t) (y3 t)) (Icc 0 T) t)
    (hL2 : ∀ u, |u| ≤ h / 2 → L2 ≤ evalQ p2 u) (hU2 : ∀ u, |u| ≤ h / 2 → evalQ p2 u ≤ U2)
    (hL3 : ∀ u, |u| ≤ h / 2 → L3 ≤ evalQ p3 u) (hU3 : ∀ u, |u| ≤ h / 2 → evalQ p3 u ≤ U3)
    (hdf2 : ∀ u, |u| ≤ h / 2 → |dEvalQ p2 u - robP (evalQ p2 u) (evalQ p3 u)| ≤ e2)
    (hdf3 : ∀ u, |u| ≤ h / 2 → |dEvalQ p3 u - robQ (evalQ p2 u) (evalQ p3 u)| ≤ e3)
    (hε0 : 0 < ε) (hε : d ^ 2 * e2 ^ 2 + e3 ^ 2 < ε ^ 2)
    (hμ : 0 < μ) (hμh : μ * h ≤ 1)
    (hA : A ≤ 1 / 25 + 10000 * L3 + 2 * 30000000 * L2)
    (hC1 : |-(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * L2 + 2 * 30000000 * L2| ≤ Cm)
    (hC2 : |-(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * U2 + 2 * 30000000 * U2| ≤ Cm)
    (hcond : Cm ^ 2 ≤ 4 * μ * (d ^ 2 * A
      - ((d ^ 2 * 10000 + 30000000) + d ^ 2 * 30000000 * (1 / d)) * B + d ^ 2 * μ))
    (hbox : -1 / 1000 ≤ L2 - B / d ∧ U2 + B / d ≤ 1 / 1000 ∧ -1 / 10 ≤ L3 - B ∧ U3 + B ≤ 11 / 10)
    (hΔ : 0 ≤ Δ) (hstart : d ^ 2 * (y2 t0 - c2) ^ 2 + (y3 t0 - c3) ^ 2 ≤ Δ ^ 2)
    (hδ0 : 0 < δ)
    (hδ : Δ + d * |c2 - evalQ p2 (-(h / 2))| + |c3 - evalQ p3 (-(h / 2))| ≤ δ)
    (hBb : (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) ≤ B) :
    ∀ t ∈ Icc t0 (t0 + h), d ^ 2 * (y2 t - evalQ p2 (t - (t0 + h / 2))) ^ 2
      + (y3 t - evalQ p3 (t - (t0 + h / 2))) ^ 2 ≤ B ^ 2 := by
  have hB0 : 0 ≤ B := (R_leD hδ0 hε0 hμ le_rfl hh.le hμh hBb).1.trans
    (R_leD hδ0 hε0 hμ le_rfl hh.le hμh hBb).2
  have hsub : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0 hT
  have hu : ∀ t ∈ Icc t0 (t0 + h), |t - (t0 + h / 2)| ≤ h / 2 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  -- polynomial point lies in the box, with room B/d and B
  have hgbox : ∀ t ∈ Icc t0 (t0 + h), ∀ z2 z3 : ℝ,
      |z2 - evalQ p2 (t - (t0 + h / 2))| ≤ B / d → |z3 - evalQ p3 (t - (t0 + h / 2))| ≤ B →
      P z2 z3 = robP z2 z3 ∧ Q z2 z3 = robQ z2 z3 := fun t ht z2 z3 hz2 hz3 => by
    have a := hL2 _ (hu t ht); have b := hU2 _ (hu t ht)
    have c := hL3 _ (hu t ht); have d := hU3 _ (hu t ht)
    rw [abs_le] at hz2 hz3
    obtain ⟨k1, k2, k3, k4⟩ := hbox
    exact hP z2 z3 (by linarith [hz2.1]) (by linarith [hz2.2]) (by linarith [hz3.1])
      (by linarith [hz3.2])
  have hgP : ∀ t ∈ Icc t0 (t0 + h),
      P (evalQ p2 (t - (t0 + h / 2))) (evalQ p3 (t - (t0 + h / 2)))
        = robP (evalQ p2 (t - (t0 + h / 2))) (evalQ p3 (t - (t0 + h / 2))) ∧
      Q (evalQ p2 (t - (t0 + h / 2))) (evalQ p3 (t - (t0 + h / 2)))
        = robQ (evalQ p2 (t - (t0 + h / 2))) (evalQ p3 (t - (t0 + h / 2))) := fun t ht =>
    hgbox t ht _ _ (by simp; positivity) (by simp; exact hB0)
  have key := Work.Sim.OneSided.onesided_cell (P := P) (Q := Q) (f2 := y2) (f3 := y3)
    (g2 := fun t => evalQ p2 (t - (t0 + h / 2))) (g3 := fun t => evalQ p3 (t - (t0 + h / 2)))
    (G2 := fun t => dEvalQ p2 (t - (t0 + h / 2))) (G3 := fun t => dEvalQ p3 (t - (t0 + h / 2)))
    (a := t0) (b := t0 + h) (w := d ^ 2) (μ := μ) (ε := ε) (δ := δ) (B := B)
    (by linarith) (by positivity) hμ.le hε0 hδ0
    (fun t ht => ((hd2 t (hsub ht)).continuousWithinAt).mono hsub)
    (fun t ht => ((hd3 t (hsub ht)).continuousWithinAt).mono hsub)
    ((continuous_evalQ p2).comp (continuous_sub_right _)).continuousOn
    ((continuous_evalQ p3).comp (continuous_sub_right _)).continuousOn
    (fun t ht => (hd2 t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht.2, ht0], by linarith [ht.1, ht.2]⟩))
    (fun t ht => (hd3 t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1, ht.2, ht0], by linarith [ht.1, ht.2]⟩))
    (fun t _ => ((hasDerivAt_evalQ p2 _).comp_sub_const t _).hasDerivWithinAt)
    (fun t _ => ((hasDerivAt_evalQ p3 _).comp_sub_const t _).hasDerivWithinAt)
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      obtain ⟨eP, eQ⟩ := hgP t ht'
      rw [eP, eQ]
      have a := sq_le_of_abs (hdf2 _ (hu t ht'))
      have b := sq_le_of_abs (hdf3 _ (hu t ht'))
      nlinarith)
    (fun t ht z2 z3 hz => by
      have ht' := Ico_subset_Icc_self ht
      obtain ⟨hb2, hb3⟩ := ball_compD hd hB0 hz
      obtain ⟨eP, eQ⟩ := hgP t ht'
      obtain ⟨eP', eQ'⟩ := hgbox t ht' z2 z3 hb2 hb3
      rw [eP, eQ, eP', eQ']
      have a := hL2 _ (hu t ht'); have b := hU2 _ (hu t ht')
      have c := hL3 _ (hu t ht')
      have hr := Work.Sim.OneSided.rob_onesided (w := d ^ 2) (s := 1 / d) (μ := μ) (B := B)
        (A := A) (Cm := Cm) (x2 := evalQ p2 (t - (t0 + h / 2)))
        (x3 := evalQ p3 (t - (t0 + h / 2))) (h2 := z2 - evalQ p2 (t - (t0 + h / 2)))
        (h3 := z3 - evalQ p3 (t - (t0 + h / 2))) (by positivity) hB0 (by positivity)
        (by field_simp; rfl)
        hμ (by linarith) (C_boundD a b hC1 hC2) hcond hz
      simp only [add_sub_cancel] at hr
      unfold robP robQ
      linarith)
    (by
      have e1 : t0 - (t0 + h / 2) = -(h / 2) := by ring
      rw [e1]
      have hm := mink (w := d ^ 2) (d := d) (x2 := y2 t0) (x3 := y3 t0) (g2 := c2) (g3 := c3)
        (c2 := evalQ p2 (-(h / 2))) (c3 := evalQ p3 (-(h / 2))) (R := Δ) hd.le
        rfl hΔ hstart
      refine hm.trans ?_
      have : 0 ≤ Δ + d * |c2 - evalQ p2 (-(h / 2))| + |c3 - evalQ p3 (-(h / 2))| := by positivity
      exact pow_le_pow_left₀ this hδ 2)
    (by
      have e1 : t0 + h - t0 = h := by ring
      rw [e1]
      exact (R_leD hδ0 hε0 hμ hh.le le_rfl hμh hBb).2)
  intro t ht
  have k := key t ht
  have hR := R_leD hδ0 hε0 hμ (x := t - t0) (by linarith [ht.1]) (by linarith [ht.2]) hμh hBb
  exact k.trans (pow_le_pow_left₀ hR.1 hR.2 2)

/-- One cell step from a rounded centre (c₂, c₃) at t₀ to a rounded centre (n₂, n₃) at t₀ + h,
in the weighted norm d ^ 2·e₂² + e₃² (wrapper of `cell` and `mink`). -/
theorem stepD (p2 p3 : List ℚ) (hd : 0 < d) {P Q : ℝ → ℝ → ℝ}
    (hP : ∀ y2 y3, -1 / 1000 ≤ y2 → y2 ≤ 1 / 1000 → -1 / 10 ≤ y3 → y3 ≤ 11 / 10 →
      P y2 y3 = robP y2 y3 ∧ Q y2 y3 = robQ y2 y3)
    {T t0 h Δ δ ε μ B A Cm L2 U2 L3 U3 e2 e3 c2 c3 n2 n3 Δ' : ℝ} {y2 y3 : ℝ → ℝ}
    (ht0 : 0 ≤ t0) (hT : t0 + h ≤ T) (hh : 0 < h)
    (hd2 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y2 (P (y2 t) (y3 t)) (Icc 0 T) t)
    (hd3 : ∀ t ∈ Icc 0 T, HasDerivWithinAt y3 (Q (y2 t) (y3 t)) (Icc 0 T) t)
    (hL2 : ∀ u, |u| ≤ h / 2 → L2 ≤ evalQ p2 u) (hU2 : ∀ u, |u| ≤ h / 2 → evalQ p2 u ≤ U2)
    (hL3 : ∀ u, |u| ≤ h / 2 → L3 ≤ evalQ p3 u) (hU3 : ∀ u, |u| ≤ h / 2 → evalQ p3 u ≤ U3)
    (hdf2 : ∀ u, |u| ≤ h / 2 → |dEvalQ p2 u - robP (evalQ p2 u) (evalQ p3 u)| ≤ e2)
    (hdf3 : ∀ u, |u| ≤ h / 2 → |dEvalQ p3 u - robQ (evalQ p2 u) (evalQ p3 u)| ≤ e3)
    (hε0 : 0 < ε) (hε : d ^ 2 * e2 ^ 2 + e3 ^ 2 < ε ^ 2)
    (hμ : 0 < μ) (hμh : μ * h ≤ 1)
    (hA : A ≤ 1 / 25 + 10000 * L3 + 2 * 30000000 * L2)
    (hC1 : |-(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * L2 + 2 * 30000000 * L2| ≤ Cm)
    (hC2 : |-(d ^ 2 * (1 / 25)) - d ^ 2 * 10000 * U2 + 2 * 30000000 * U2| ≤ Cm)
    (hcond : Cm ^ 2 ≤ 4 * μ * (d ^ 2 * A
      - ((d ^ 2 * 10000 + 30000000) + d ^ 2 * 30000000 * (1 / d)) * B + d ^ 2 * μ))
    (hbox : -1 / 1000 ≤ L2 - B / d ∧ U2 + B / d ≤ 1 / 1000 ∧ -1 / 10 ≤ L3 - B ∧ U3 + B ≤ 11 / 10)
    (hΔ : 0 ≤ Δ) (hstart : d ^ 2 * (y2 t0 - c2) ^ 2 + (y3 t0 - c3) ^ 2 ≤ Δ ^ 2)
    (hδ0 : 0 < δ)
    (hδ : Δ + d * |c2 - evalQ p2 (-(h / 2))| + |c3 - evalQ p3 (-(h / 2))| ≤ δ)
    (hBb : (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) ≤ B)
    (hn : B + d * |evalQ p2 (h / 2) - n2| + |evalQ p3 (h / 2) - n3| ≤ Δ') :
    (∀ t ∈ Icc t0 (t0 + h), -1 / 1000 ≤ y2 t ∧ y2 t ≤ 1 / 1000 ∧ -1 / 10 ≤ y3 t ∧ y3 t ≤ 11 / 10) ∧
    d ^ 2 * (y2 (t0 + h) - n2) ^ 2 + (y3 (t0 + h) - n3) ^ 2 ≤ Δ' ^ 2 := by
  have hall := cellD p2 p3 hd hP ht0 hT hh hd2 hd3 hL2 hU2 hL3 hU3 hdf2 hdf3 hε0 hε hμ hμh hA hC1 hC2
    hcond hbox hΔ hstart hδ0 hδ hBb
  have hB0 : 0 ≤ B := by
    have : 0 < (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) := by positivity
    linarith
  refine ⟨fun t ht => ?_, ?_⟩
  · have hu : |t - (t0 + h / 2)| ≤ h / 2 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    obtain ⟨b2, b3⟩ := ball_compD hd hB0 (hall t ht)
    have l2 := hL2 _ hu
    have u2 := hU2 _ hu
    have l3 := hL3 _ hu
    have u3 := hU3 _ hu
    rw [abs_le] at b2 b3
    obtain ⟨x1, x2, x3, x4⟩ := hbox
    exact ⟨by linarith [b2.1], by linarith [b2.2], by linarith [b3.1], by linarith [b3.2]⟩
  have hc := hall (t0 + h) ⟨by linarith, le_rfl⟩
  rw [show t0 + h - (t0 + h / 2) = h / 2 by ring] at hc
  have hm := mink (c2 := n2) (c3 := n3) (d := d) hd.le rfl hB0 hc
  exact hm.trans (pow_le_pow_left₀ (by positivity) hn 2)

end Work.Sim.RobCellD

#print axioms Work.Sim.RobCellD.stepD
#print axioms Work.Sim.RobCellD.weight_down
