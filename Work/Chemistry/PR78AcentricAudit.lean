import Mathlib
import Work.Chemistry.PR78Acentric
import Work.Chemistry.PR78AcentricBlind

/-!
# Audit (run 2026-11-05T1828Z): the blind restatement of the PR 1978 ω = 1 claim, closed

`Work/Chemistry/PR78AcentricBlind.lean` was written by a blind restater (Sonnet) from the claim in
words only (notes `runs/2026-11-05T1828Z/blind/notes_pr78.md`); it is copied verbatim from
`runs/2026-11-05T1828Z/blind/`. Its two theorems are proved here from the frozen headlines
`Work.Chemistry.PR78Acentric.pr78_omega1_unique` and `pr78_omega1_exists`
(`closed_pr78_acentric`, `closed_pr78_exists`; types matched by `rfl` at the end).
-/

namespace Work.Chemistry.PR78AcentricAudit
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence Blind.PR78Acentric

lemma iso_c (R a_c b κ Tc : ℝ) (hTc : 0 < Tc) :
    (fun v => P R a_c b Tc κ v Tc) = cubicP R a_c b 2 (-1) Tc := by
  funext v
  have : Tc / Tc = 1 := div_self hTc.ne'
  simp only [P, aT, cubicP, this, Real.sqrt_one, sub_self, mul_zero, add_zero, one_pow, mul_one]
  ring_nf

lemma iso_7 (R a_c b Tc : ℝ) (hTc : 0 < Tc) :
    (fun v => P R a_c b Tc (kappa 1) v (0.7 * Tc)) =
      cubicP R (a_c * (1 + (0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc) := by
  funext v
  have : 7 / 10 * Tc / Tc = 7 / 10 := by field_simp
  have h7 : (0.7 : ℝ) * Tc = 7 / 10 * Tc := by norm_num
  simp only [P, aT, cubicP, kappa, this, h7]
  ring_nf

lemma crit (R a_c b Tc vc : ℝ) (hc : IsCritical R a_c b (kappa 1) Tc vc) :
    0 < Tc ∧ b < vc ∧ IsCriticalIsotherm (cubicP R a_c b 2 (-1) Tc) vc := by
  obtain ⟨hT, hv, h1, h2⟩ := hc
  rw [iso_c R a_c b (kappa 1) Tc hT] at h1 h2
  exact ⟨hT, hv, h1, h2⟩

lemma maxwell (R a_c b Tc vl vg ps : ℝ) (hTc : 0 < Tc)
    (h : IsMaxwell R a_c b Tc (kappa 1) (0.7 * Tc) vl vg ps) :
    b < vl ∧ IsMaxwellCoexistence
      (cubicP R (a_c * (1 + (0.379642 + 1.48503 * 1 - 0.164423 * 1 ^ 2 + 0.016666 * 1 ^ 3) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 2 (-1) (7 / 10 * Tc)) vl vg ps := by
  obtain ⟨hl, hlg, h1, h2, h3⟩ := h
  have e := iso_7 R a_c b Tc hTc
  refine ⟨hl, hlg, ?_, ?_, ?_⟩
  · rw [← congrFun e vl]; exact h1
  · rw [← congrFun e vg]; exact h2
  · rw [← e]; exact h3

lemma pc_eq (R a_c b Tc vc : ℝ) (hT : 0 < Tc) :
    P R a_c b Tc (kappa 1) vc Tc = cubicP R a_c b 2 (-1) Tc vc :=
  congrFun (iso_c R a_c b (kappa 1) Tc hT) vc

theorem closed_pr78_acentric (R a_c b T_c v_c v_l v_g p_s : ℝ)
    (hR : 0 < R) (ha : 0 < a_c) (hb : 0 < b)
    (hcrit : IsCritical R a_c b (kappa 1) T_c v_c)
    (hmax : IsMaxwell R a_c b T_c (kappa 1) (0.7 * T_c) v_l v_g p_s) :
    RoundsTo (p_s / P R a_c b T_c (kappa 1) v_c T_c) 0.0100 4 ∧
    RoundsTo (-Real.logb 10 (p_s / P R a_c b T_c (kappa 1) v_c T_c) - 1) 1.000 3 := by
  obtain ⟨hT, hv, hcr⟩ := crit R a_c b T_c v_c hcrit
  obtain ⟨hl, hM⟩ := maxwell R a_c b T_c v_l v_g p_s hT hmax
  rw [pc_eq R a_c b T_c v_c hT]
  exact Work.Chemistry.PR78Acentric.pr78_omega1_unique R a_c b T_c v_c v_l v_g p_s ha hb hv hcr hl hM

theorem closed_pr78_exists (R a_c b T_c v_c : ℝ)
    (hR : 0 < R) (ha : 0 < a_c) (hb : 0 < b)
    (hcrit : IsCritical R a_c b (kappa 1) T_c v_c) :
    ∃ v_l v_g p_s : ℝ, IsMaxwell R a_c b T_c (kappa 1) (0.7 * T_c) v_l v_g p_s ∧
      RoundsTo (p_s / P R a_c b T_c (kappa 1) v_c T_c) 0.0100 4 ∧
      RoundsTo (-Real.logb 10 (p_s / P R a_c b T_c (kappa 1) v_c T_c) - 1) 1.000 3 := by
  obtain ⟨hT, hv, hcr⟩ := crit R a_c b T_c v_c hcrit
  obtain ⟨vl, vg, ps, hl, ⟨hlg, h1, h2, h3⟩, r1, r2⟩ :=
    Work.Chemistry.PR78Acentric.pr78_omega1_exists R a_c b T_c v_c ha hb hv hcr
  have e := iso_7 R a_c b T_c hT
  refine ⟨vl, vg, ps, ⟨hl, hlg, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [congrFun e vl]; exact h1
  · rw [congrFun e vg]; exact h2
  · rw [e]; exact h3
  · rw [pc_eq R a_c b T_c v_c hT]; exact r1
  · rw [pc_eq R a_c b T_c v_c hT]; exact r2

/-- The closures have exactly the types of the blind theorems. -/
example : type_of% @closed_pr78_acentric = type_of% @Blind.PR78Acentric.pr78_acentric := rfl
example : type_of% @closed_pr78_exists = type_of% @Blind.PR78Acentric.pr78_exists := rfl

end Work.Chemistry.PR78AcentricAudit
