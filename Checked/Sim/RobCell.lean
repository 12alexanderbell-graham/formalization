import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Bound
import Checked.Sim.ODETools
import Checked.Sim.OneSided

/-!
# Robertson network: the validated one-sided cell step

Reduced Robertson field in (y₂, y₃) with y₁ = 1 − y₂ − y₃ (`robP`, `robQ`). `cell`: one
logarithmic-norm step (`Checked.Sim.OneSided.onesided_cell`, weighted norm 4900·e₂² + e₃²) from a
rational polynomial approximation centred at the cell midpoint, with certified defect and a
rational one-sided condition (`Checked.Sim.OneSided.rob_onesided`). It holds for every field that
equals the Robertson field on a fixed box containing every tube, so it also applies to a
clamped field (existence).
-/

namespace Checked.Sim.RobCell
open Set Checked.Sim

/-- Reduced Robertson field, first component (y₂′ with y₁ = 1 − y₂ − y₃). -/
noncomputable def robP (y2 y3 : ℝ) : ℝ := 1 / 25 * (1 - y2 - y3) - 10000 * y2 * y3 - 30000000 * y2 ^ 2

/-- Reduced Robertson field, second component (y₃′). -/
noncomputable def robQ (y2 y3 : ℝ) : ℝ := 30000000 * y2 ^ 2

theorem abs_evalQ_le_sym (cs : List ℚ) {u r : ℝ} (hu : |u| ≤ r) :
    |evalQ cs u| ≤ evalQ (cs.map (fun c => |c|)) r := by
  induction cs with
  | nil => simp [evalQ]
  | cons c cs ih =>
    simp only [evalQ, List.map_cons, Rat.cast_abs]
    have hA : 0 ≤ evalQ (cs.map (fun c => |c|)) r := (abs_nonneg _).trans ih
    calc |(c : ℝ) + u * evalQ cs u| ≤ |(c : ℝ)| + |u * evalQ cs u| := abs_add_le _ _
      _ = |(c : ℝ)| + |u| * |evalQ cs u| := by rw [abs_mul]
      _ ≤ |(c : ℝ)| + r * evalQ (cs.map (fun c => |c|)) r :=
          add_le_add_right ((mul_le_mul_of_nonneg_left ih (abs_nonneg u)).trans
            (mul_le_mul_of_nonneg_right hu hA)) _

theorem tail_bound (cs : List ℚ) {u r : ℝ} (hu : |u| ≤ r) :
    |u * evalQ cs u| ≤ r * evalQ (cs.map (fun c => |c|)) r := by
  have h1 := abs_evalQ_le_sym cs hu
  have hA : 0 ≤ evalQ (cs.map (fun c => |c|)) r := (abs_nonneg _).trans h1
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg u)).trans (mul_le_mul_of_nonneg_right hu hA)

theorem lower_sym (p : List ℚ) {u r : ℝ} (hu : |u| ≤ r) :
    ((p.headD 0 : ℚ) : ℝ) - r * evalQ (p.tail.map (fun c => |c|)) r ≤ evalQ p u := by
  cases p with
  | nil =>
    have : 0 ≤ r := (abs_nonneg u).trans hu
    simp [evalQ]
  | cons c cs =>
    have := tail_bound cs hu
    simp only [List.headD_cons, List.tail_cons, evalQ]
    linarith [neg_abs_le (u * evalQ cs u)]

theorem upper_sym (p : List ℚ) {u r : ℝ} (hu : |u| ≤ r) :
    evalQ p u ≤ ((p.headD 0 : ℚ) : ℝ) + r * evalQ (p.tail.map (fun c => |c|)) r := by
  cases p with
  | nil =>
    have : 0 ≤ r := (abs_nonneg u).trans hu
    simp [evalQ]
  | cons c cs =>
    have := tail_bound cs hu
    simp only [List.headD_cons, List.tail_cons, evalQ]
    linarith [le_abs_self (u * evalQ cs u)]

theorem abs_le_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : |a| ≤ b := by
  have := sq_le_sq.mp h
  rwa [abs_of_nonneg hb] at this

theorem mink {w d x2 x3 g2 g3 c2 c3 R : ℝ} (hd : 0 ≤ d) (hw : w = d ^ 2) (hR : 0 ≤ R)
    (h : w * (x2 - g2) ^ 2 + (x3 - g3) ^ 2 ≤ R ^ 2) :
    w * (x2 - c2) ^ 2 + (x3 - c3) ^ 2 ≤ (R + d * |g2 - c2| + |g3 - c3|) ^ 2 := by
  subst hw
  have ha2 : (d * (x2 - g2)) ^ 2 ≤ R ^ 2 := by
    have : (d * (x2 - g2)) ^ 2 = d ^ 2 * (x2 - g2) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg (x3 - g3)]
  have hb2 : (x3 - g3) ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg (x2 - g2), sq_nonneg d]
  have ha := abs_le_of_sq hR ha2
  have hb := abs_le_of_sq hR hb2
  have hp : |d * (g2 - c2)| = d * |g2 - c2| := by rw [abs_mul, abs_of_nonneg hd]
  -- cross terms
  have c1 : (d * (x2 - g2)) * (d * (g2 - c2)) ≤ R * (d * |g2 - c2|) := by
    rw [← hp]
    calc (d * (x2 - g2)) * (d * (g2 - c2)) ≤ |(d * (x2 - g2)) * (d * (g2 - c2))| := le_abs_self _
      _ = |d * (x2 - g2)| * |d * (g2 - c2)| := abs_mul _ _
      _ ≤ R * |d * (g2 - c2)| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have c2' : (x3 - g3) * (g3 - c3) ≤ R * |g3 - c3| := by
    calc (x3 - g3) * (g3 - c3) ≤ |(x3 - g3) * (g3 - c3)| := le_abs_self _
      _ = |x3 - g3| * |g3 - c3| := abs_mul _ _
      _ ≤ R * |g3 - c3| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have sp : (d * (g2 - c2)) ^ 2 = (d * |g2 - c2|) ^ 2 := by rw [← hp, sq_abs]
  have sq3 : (g3 - c3) ^ 2 = |g3 - c3| ^ 2 := (sq_abs _).symm
  have hpq : 0 ≤ (d * |g2 - c2|) * |g3 - c3| := mul_nonneg (mul_nonneg hd (abs_nonneg _)) (abs_nonneg _)
  have e : d ^ 2 * (x2 - c2) ^ 2 + (x3 - c3) ^ 2
      = (d ^ 2 * (x2 - g2) ^ 2 + (x3 - g3) ^ 2)
        + 2 * ((d * (x2 - g2)) * (d * (g2 - c2)) + (x3 - g3) * (g3 - c3))
        + ((d * (g2 - c2)) ^ 2 + (g3 - c3) ^ 2) := by ring
  rw [e, sp, sq3]
  have e2 : (R + d * |g2 - c2| + |g3 - c3|) ^ 2
      = R ^ 2 + 2 * (R * (d * |g2 - c2|) + R * |g3 - c3|)
        + ((d * |g2 - c2|) ^ 2 + |g3 - c3| ^ 2 + 2 * ((d * |g2 - c2|) * |g3 - c3|)) := by ring
  rw [e2]
  linarith

theorem exp_le_quad {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  have := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at this
  nlinarith [sq_nonneg x]

theorem sq_le_of_abs {x e : ℝ} (h : |x| ≤ e) : x ^ 2 ≤ e ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg x) h 2

/-- The affine coefficient C(x) of the one-sided form is bounded by its endpoint values. -/
theorem C_bound {L U x Cm : ℝ} (hL : L ≤ x) (hU : x ≤ U)
    (h1 : |-(4900 * (1 / 25)) - 4900 * 10000 * L + 2 * 30000000 * L| ≤ Cm)
    (h2 : |-(4900 * (1 / 25)) - 4900 * 10000 * U + 2 * 30000000 * U| ≤ Cm) :
    |-(4900 * (1 / 25)) - 4900 * 10000 * x + 2 * 30000000 * x| ≤ Cm := by
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Weighted ball: componentwise bounds. -/
theorem ball_comp {h2 h3 B : ℝ} (hB : 0 ≤ B) (hh : 4900 * h2 ^ 2 + h3 ^ 2 ≤ B ^ 2) :
    |h2| ≤ B / 70 ∧ |h3| ≤ B := by
  constructor
  · have : (70 * h2) ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg h3]
    have h := abs_le_of_sq hB this
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 70)] at h
    linarith
  · exact abs_le_of_sq hB (by nlinarith [sq_nonneg h2])

/-- Monotone bound R(t) ≤ R(b). -/
theorem R_le {δ ε μ x h B : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hμ : 0 < μ) (hx0 : 0 ≤ x) (hxh : x ≤ h)
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

theorem cell (p2 p3 : List ℚ) {P Q : ℝ → ℝ → ℝ}
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
    (hε0 : 0 < ε) (hε : 4900 * e2 ^ 2 + e3 ^ 2 < ε ^ 2)
    (hμ : 0 < μ) (hμh : μ * h ≤ 1)
    (hA : A ≤ 1 / 25 + 10000 * L3 + 2 * 30000000 * L2)
    (hC1 : |-(4900 * (1 / 25)) - 4900 * 10000 * L2 + 2 * 30000000 * L2| ≤ Cm)
    (hC2 : |-(4900 * (1 / 25)) - 4900 * 10000 * U2 + 2 * 30000000 * U2| ≤ Cm)
    (hcond : Cm ^ 2 ≤ 4 * μ * (4900 * A
      - ((4900 * 10000 + 30000000) + 4900 * 30000000 * (1 / 70)) * B + 4900 * μ))
    (hbox : -1 / 1000 ≤ L2 - B / 70 ∧ U2 + B / 70 ≤ 1 / 1000 ∧ -1 / 10 ≤ L3 - B ∧ U3 + B ≤ 11 / 10)
    (hΔ : 0 ≤ Δ) (hstart : 4900 * (y2 t0 - c2) ^ 2 + (y3 t0 - c3) ^ 2 ≤ Δ ^ 2)
    (hδ0 : 0 < δ)
    (hδ : Δ + 70 * |c2 - evalQ p2 (-(h / 2))| + |c3 - evalQ p3 (-(h / 2))| ≤ δ)
    (hBb : (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) ≤ B) :
    ∀ t ∈ Icc t0 (t0 + h), 4900 * (y2 t - evalQ p2 (t - (t0 + h / 2))) ^ 2
      + (y3 t - evalQ p3 (t - (t0 + h / 2))) ^ 2 ≤ B ^ 2 := by
  have hB0 : 0 ≤ B := (R_le hδ0 hε0 hμ le_rfl hh.le hμh hBb).1.trans
    (R_le hδ0 hε0 hμ le_rfl hh.le hμh hBb).2
  have hsub : Icc t0 (t0 + h) ⊆ Icc 0 T := Icc_subset_Icc ht0 hT
  have hu : ∀ t ∈ Icc t0 (t0 + h), |t - (t0 + h / 2)| ≤ h / 2 := fun t ht => by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  -- polynomial point lies in the box, with room B/70 and B
  have hgbox : ∀ t ∈ Icc t0 (t0 + h), ∀ z2 z3 : ℝ,
      |z2 - evalQ p2 (t - (t0 + h / 2))| ≤ B / 70 → |z3 - evalQ p3 (t - (t0 + h / 2))| ≤ B →
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
  have key := Checked.Sim.OneSided.onesided_cell (P := P) (Q := Q) (f2 := y2) (f3 := y3)
    (g2 := fun t => evalQ p2 (t - (t0 + h / 2))) (g3 := fun t => evalQ p3 (t - (t0 + h / 2)))
    (G2 := fun t => dEvalQ p2 (t - (t0 + h / 2))) (G3 := fun t => dEvalQ p3 (t - (t0 + h / 2)))
    (a := t0) (b := t0 + h) (w := 4900) (μ := μ) (ε := ε) (δ := δ) (B := B)
    (by linarith) (by norm_num) hμ.le hε0 hδ0
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
      obtain ⟨hb2, hb3⟩ := ball_comp hB0 hz
      obtain ⟨eP, eQ⟩ := hgP t ht'
      obtain ⟨eP', eQ'⟩ := hgbox t ht' z2 z3 hb2 hb3
      rw [eP, eQ, eP', eQ']
      have a := hL2 _ (hu t ht'); have b := hU2 _ (hu t ht')
      have c := hL3 _ (hu t ht')
      have hr := Checked.Sim.OneSided.rob_onesided (w := 4900) (s := 1 / 70) (μ := μ) (B := B)
        (A := A) (Cm := Cm) (x2 := evalQ p2 (t - (t0 + h / 2)))
        (x3 := evalQ p3 (t - (t0 + h / 2))) (h2 := z2 - evalQ p2 (t - (t0 + h / 2)))
        (h3 := z3 - evalQ p3 (t - (t0 + h / 2))) (by norm_num) hB0 (by norm_num) (by norm_num)
        hμ (by linarith) (C_bound a b hC1 hC2) hcond hz
      simp only [add_sub_cancel] at hr
      unfold robP robQ
      linarith)
    (by
      have e1 : t0 - (t0 + h / 2) = -(h / 2) := by ring
      rw [e1]
      have hm := mink (w := 4900) (d := 70) (x2 := y2 t0) (x3 := y3 t0) (g2 := c2) (g3 := c3)
        (c2 := evalQ p2 (-(h / 2))) (c3 := evalQ p3 (-(h / 2))) (R := Δ) (by norm_num)
        (by norm_num) hΔ hstart
      refine hm.trans ?_
      have : 0 ≤ Δ + 70 * |c2 - evalQ p2 (-(h / 2))| + |c3 - evalQ p3 (-(h / 2))| := by positivity
      exact pow_le_pow_left₀ this hδ 2)
    (by
      have e1 : t0 + h - t0 = h := by ring
      rw [e1]
      exact (R_le hδ0 hε0 hμ hh.le le_rfl hμh hBb).2)
  intro t ht
  have k := key t ht
  have hR := R_le hδ0 hε0 hμ (x := t - t0) (by linarith [ht.1]) (by linarith [ht.2]) hμh hBb
  exact k.trans (pow_le_pow_left₀ hR.1 hR.2 2)

/-- One cell step from a rounded centre (c₂, c₃) at t₀ to a rounded centre (n₂, n₃) at t₀ + h,
in the weighted norm 4900·e₂² + e₃² (wrapper of `cell` and `mink`). -/
theorem step (p2 p3 : List ℚ) {P Q : ℝ → ℝ → ℝ}
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
    (hε0 : 0 < ε) (hε : 4900 * e2 ^ 2 + e3 ^ 2 < ε ^ 2)
    (hμ : 0 < μ) (hμh : μ * h ≤ 1)
    (hA : A ≤ 1 / 25 + 10000 * L3 + 2 * 30000000 * L2)
    (hC1 : |-(4900 * (1 / 25)) - 4900 * 10000 * L2 + 2 * 30000000 * L2| ≤ Cm)
    (hC2 : |-(4900 * (1 / 25)) - 4900 * 10000 * U2 + 2 * 30000000 * U2| ≤ Cm)
    (hcond : Cm ^ 2 ≤ 4 * μ * (4900 * A
      - ((4900 * 10000 + 30000000) + 4900 * 30000000 * (1 / 70)) * B + 4900 * μ))
    (hbox : -1 / 1000 ≤ L2 - B / 70 ∧ U2 + B / 70 ≤ 1 / 1000 ∧ -1 / 10 ≤ L3 - B ∧ U3 + B ≤ 11 / 10)
    (hΔ : 0 ≤ Δ) (hstart : 4900 * (y2 t0 - c2) ^ 2 + (y3 t0 - c3) ^ 2 ≤ Δ ^ 2)
    (hδ0 : 0 < δ)
    (hδ : Δ + 70 * |c2 - evalQ p2 (-(h / 2))| + |c3 - evalQ p3 (-(h / 2))| ≤ δ)
    (hBb : (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) ≤ B)
    (hn : B + 70 * |evalQ p2 (h / 2) - n2| + |evalQ p3 (h / 2) - n3| ≤ Δ') :
    (∀ t ∈ Icc t0 (t0 + h), -1 / 1000 ≤ y2 t ∧ y2 t ≤ 1 / 1000 ∧ -1 / 10 ≤ y3 t ∧ y3 t ≤ 11 / 10) ∧
    4900 * (y2 (t0 + h) - n2) ^ 2 + (y3 (t0 + h) - n3) ^ 2 ≤ Δ' ^ 2 := by
  have hall := cell p2 p3 hP ht0 hT hh hd2 hd3 hL2 hU2 hL3 hU3 hdf2 hdf3 hε0 hε hμ hμh hA hC1 hC2
    hcond hbox hΔ hstart hδ0 hδ hBb
  have hB0 : 0 ≤ B := by
    have : 0 < (δ + ε * h) * (1 + μ * h + (μ * h) ^ 2) := by positivity
    linarith
  refine ⟨fun t ht => ?_, ?_⟩
  · have hu : |t - (t0 + h / 2)| ≤ h / 2 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    obtain ⟨b2, b3⟩ := ball_comp hB0 (hall t ht)
    have l2 := hL2 _ hu
    have u2 := hU2 _ hu
    have l3 := hL3 _ hu
    have u3 := hU3 _ hu
    rw [abs_le] at b2 b3
    obtain ⟨x1, x2, x3, x4⟩ := hbox
    exact ⟨by linarith [b2.1], by linarith [b2.2], by linarith [b3.1], by linarith [b3.2]⟩
  have hc := hall (t0 + h) ⟨by linarith, le_rfl⟩
  rw [show t0 + h - (t0 + h / 2) = h / 2 by ring] at hc
  have hm := mink (c2 := n2) (c3 := n3) (d := 70) (by norm_num) (by norm_num) hB0 hc
  exact hm.trans (pow_le_pow_left₀ (by positivity) hn 2)

end Checked.Sim.RobCell
