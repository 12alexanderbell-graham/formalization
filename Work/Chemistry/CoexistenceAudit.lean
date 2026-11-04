import Work.Chemistry.CoexistenceBlind
import Work.Chemistry.Coexistence
import Work.Chemistry.CoexistenceExists

/-!
# Blind restatement of `Work.Chemistry.Coexistence` closed in Lean (run 2026-11-04T0028Z)

The blind restater (run 2026-10-31T1428Z, `runs/2026-10-31T1428Z/blind/CoexistenceBlind.lean`,
copied verbatim to `Work/Chemistry/CoexistenceBlind.lean`; textbook claims only) stated
coexistence by **equal molar Gibbs energy** with an explicit Helmholtz energy, not by equal
areas, and added `0 < ps` and a uniqueness statement for the acentric factor. All four blind
statements are proved here from the program's frozen theorems (`vdW_coexistence_exists`,
`vdW_coexistence_unique`) and `acentric_window`; the bridge is the blind restater's own
modelling lemma (equal Gibbs energy ⇔ equal areas, by the fundamental theorem of calculus).
-/

namespace Work.Chemistry.CoexistenceAudit

open Blind.Coexistence Checked.Records Checked.Chemistry.CubicEOS

/-- The blind restater's modelling lemma, proved. -/
theorem equalGibbs_iff_equalArea_closed (R a b T vl vg ps : ℝ) (hb : 0 < b)
    (hl : b < vl) (hlg : vl < vg)
    (hpl : vdwP R a b T vl = ps) (hpg : vdwP R a b T vg = ps) :
    gibbs R a b T vl = gibbs R a b T vg ↔
      ∫ v in vl..vg, vdwP R a b T v = ps * (vg - vl) := by
  have hderiv : ∀ x ∈ Set.uIcc vl vg,
      HasDerivAt (fun y => R * T * Real.log (y - b) + a * y⁻¹) (vdwP R a b T x) x := by
    intro x hx
    rw [Set.uIcc_of_le hlg.le] at hx
    have h1 : x - b ≠ 0 := sub_ne_zero.2 (ne_of_gt (by linarith [hx.1] : b < x))
    have h0 : x ≠ 0 := ne_of_gt (by linarith [hx.1] : 0 < x)
    have hL := ((hasDerivAt_id x).sub_const b).log h1
    have hB := (hasDerivAt_inv h0).const_mul a
    convert (hL.const_mul (R * T)).add hB using 1
    all_goals first
      | rfl
      | (funext y; simp)
      | (unfold vdwP; field_simp; ring)
  have hcont : ContinuousOn (fun v => vdwP R a b T v) (Set.uIcc vl vg) := by
    rw [Set.uIcc_of_le hlg.le]
    unfold vdwP
    apply ContinuousOn.sub
    · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
        (fun x hx => sub_ne_zero.2 (ne_of_gt (by linarith [hx.1] : b < x)))
    · exact continuousOn_const.div (continuousOn_id.pow 2)
        (fun x hx => pow_ne_zero 2 (ne_of_gt (by linarith [hx.1] : 0 < x)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  unfold gibbs
  rw [hpl, hpg]
  simp only [div_eq_mul_inv]
  constructor <;> intro h <;> linear_combination h

lemma vdwP_eq (R a b v : ℝ) :
    vdwP R a b (7 / 10 * Tc R a b) v = cubicP R a b 0 0 (7 / 10 * (8 * a / (27 * R * b))) v := by
  unfold vdwP cubicP Tc; simp

lemma pos_of_round {x : ℝ} (h : RoundsTo x 0.20046 5) :
    40091 / 200000 ≤ x ∧ x ≤ 40093 / 200000 := by
  unfold RoundsTo at h
  rw [abs_le] at h
  obtain ⟨t1, t2⟩ := h
  norm_num at t1 t2
  constructor <;> linarith

/-- Blind claim 1, closed. -/
theorem coexistence_exists_closed (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) :
    ∃ vl vg ps : ℝ, IsCoexistence R a b (7 / 10 * Tc R a b) vl vg ps ∧
      0 < ps ∧
      RoundsTo (ps / Pc a b) 0.20046 5 ∧
      RoundsTo (Blind.Coexistence.acentric a b ps) (-0.3020) 4 := by
  obtain ⟨vl, vg, ps, hl, hM, h1, h2⟩ :=
    Work.Chemistry.Coexistence.vdW_coexistence_exists R a b hR ha hb
  obtain ⟨hlg, hpl, hpg, hint⟩ := hM
  have hpl' : vdwP R a b (7 / 10 * Tc R a b) vl = ps := by rw [vdwP_eq]; exact hpl
  have hpg' : vdwP R a b (7 / 10 * Tc R a b) vg = ps := by rw [vdwP_eq]; exact hpg
  have hint' : ∫ v in vl..vg, vdwP R a b (7 / 10 * Tc R a b) v = ps * (vg - vl) := by
    simp only [vdwP_eq]; exact hint
  have hPc : 0 < Pc a b := by unfold Pc; positivity
  have hw := pos_of_round (x := ps / Pc a b) h1
  have hps : 0 < ps := by
    have e : ps = ps / Pc a b * Pc a b := (div_mul_cancel₀ ps hPc.ne').symm
    rw [e]; exact mul_pos (by linarith [hw.1]) hPc
  exact ⟨vl, vg, ps, ⟨hl, hlg, hpl', hpg',
    (equalGibbs_iff_equalArea_closed R a b _ vl vg ps hb hl hlg hpl' hpg').2 hint'⟩,
    hps, h1, h2⟩

/-- Blind claim 2, closed. -/
theorem coexistence_unique_closed (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (vl vg ps : ℝ) (h : IsCoexistence R a b (7 / 10 * Tc R a b) vl vg ps) :
    RoundsTo (ps / Pc a b) 0.20046 5 := by
  obtain ⟨hl, hlg, hpl, hpg, hG⟩ := h
  have hint := (equalGibbs_iff_equalArea_closed R a b _ vl vg ps hb hl hlg hpl hpg).1 hG
  rw [vdwP_eq] at hpl hpg
  simp only [vdwP_eq] at hint
  exact Work.Chemistry.Coexistence.vdW_coexistence_unique R a b vl vg ps hR ha hb hl
    (by unfold Work.Chemistry.Coexistence.IsMaxwellCoexistence; exact ⟨hlg, hpl, hpg, hint⟩)

/-- Blind supplement (acentric factor well defined), closed. -/
theorem acentric_unique_closed (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (vl vg ps : ℝ) (h : IsCoexistence R a b (7 / 10 * Tc R a b) vl vg ps) :
    0 < ps ∧ RoundsTo (Blind.Coexistence.acentric a b ps) (-0.3020) 4 := by
  have hw := pos_of_round (coexistence_unique_closed R a b hR ha hb vl vg ps h)
  have hPc : 0 < Pc a b := by unfold Pc; positivity
  refine ⟨?_, Work.Chemistry.CoexistenceReduced.acentric_window hw.1 hw.2⟩
  have e : ps = ps / Pc a b * Pc a b := (div_mul_cancel₀ ps hPc.ne').symm
  rw [e]; exact mul_pos (by linarith [hw.1]) hPc

end Work.Chemistry.CoexistenceAudit
