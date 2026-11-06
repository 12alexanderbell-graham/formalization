import Mathlib
import Work.Chemistry.SRKAcentric
import Work.Chemistry.SRKAcentricBlind

/-!
# Audit (run 2026-11-06T0028Z): the blind restatement of the SRK ω = 1 claim, closed

`Work/Chemistry/SRKAcentricBlind.lean` was written by a blind restater (Sonnet) from the claim in
words only (notes `runs/2026-11-06T0028Z/blind/notes_srk.md`); it is copied verbatim from
`runs/2026-11-06T0028Z/blind/`. Its two theorems are proved here from the frozen headlines
`Work.Chemistry.SRKAcentric.srk_omega1_unique` and `srk_omega1_exists`
(`closed_srk_acentric`, `closed_srk_exists`; types matched by `rfl` at the end).
-/

namespace Work.Chemistry.SRKAcentricAudit
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence Blind.SRKAcentric

lemma iso_c (R ac b Tc : ℝ) (hTc : 0 < Tc) :
    (fun v => P R ac Tc b v Tc) = cubicP R ac b 1 0 Tc := by
  funext v
  have : Tc / Tc = 1 := div_self hTc.ne'
  simp only [P, aT, cubicP, this, Real.sqrt_one, sub_self, mul_zero, add_zero, one_pow, mul_one]
  ring_nf

lemma iso_7 (R ac b Tc : ℝ) (hTc : 0 < Tc) :
    (fun v => P R ac Tc b v (0.7 * Tc)) =
      cubicP R (ac * (1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc) := by
  funext v
  have : 7 / 10 * Tc / Tc = 7 / 10 := by field_simp
  have h7 : (0.7 : ℝ) * Tc = 7 / 10 * Tc := by norm_num
  simp only [P, aT, cubicP, kappa, this, h7]
  ring_nf

lemma crit (R ac b Tc vc : ℝ) (hTc : 0 < Tc) (hc : IsCritical R ac b Tc vc) :
    b < vc ∧ IsCriticalIsotherm (cubicP R ac b 1 0 Tc) vc := by
  obtain ⟨hv, h1, h2⟩ := hc
  rw [iso_c R ac b Tc hTc] at h1 h2
  exact ⟨hv, h1, h2⟩

lemma maxwell (R ac b Tc vl vg ps : ℝ) (hTc : 0 < Tc)
    (h : IsMaxwell R ac Tc b (0.7 * Tc) ps vl vg) :
    b < vl ∧ IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.480 + 1.574 * 1 - 0.176 * 1 ^ 2) *
        (1 - Real.sqrt (7 / 10))) ^ 2) b 1 0 (7 / 10 * Tc)) vl vg ps := by
  obtain ⟨hl, hlg, h1, h2, h3⟩ := h
  have e := iso_7 R ac b Tc hTc
  refine ⟨hl, hlg, ?_, ?_, ?_⟩
  · rw [← congrFun e vl]; exact h1
  · rw [← congrFun e vg]; exact h2
  · rw [← e]; exact h3

lemma pc_eq (R ac b Tc vc : ℝ) (hT : 0 < Tc) :
    P R ac Tc b vc Tc = cubicP R ac b 1 0 Tc vc :=
  congrFun (iso_c R ac b Tc hT) vc

theorem closed_srk_acentric (R ac b Tc vc : ℝ) (hR : 0 < R) (hac : 0 < ac) (hb : 0 < b)
    (hTc : 0 < Tc) (hcrit : IsCritical R ac b Tc vc)
    (ps vl vg : ℝ) (hM : IsMaxwell R ac Tc b (0.7 * Tc) ps vl vg) :
    Checked.Records.RoundsTo (ps / P R ac Tc b vc Tc) 0.0102 4 ∧
    Checked.Records.RoundsTo (-Real.logb 10 (ps / P R ac Tc b vc Tc) - 1) 0.992 3 := by
  obtain ⟨hv, hcr⟩ := crit R ac b Tc vc hTc hcrit
  obtain ⟨hl, hMx⟩ := maxwell R ac b Tc vl vg ps hTc hM
  rw [pc_eq R ac b Tc vc hTc]
  exact Work.Chemistry.SRKAcentric.srk_omega1_unique R ac b Tc vc vl vg ps hac hb hv hcr hl hMx

theorem closed_srk_exists (R ac b Tc vc : ℝ) (hR : 0 < R) (hac : 0 < ac) (hb : 0 < b)
    (hTc : 0 < Tc) (hcrit : IsCritical R ac b Tc vc) :
    ∃ ps vl vg, IsMaxwell R ac Tc b (0.7 * Tc) ps vl vg := by
  obtain ⟨hv, hcr⟩ := crit R ac b Tc vc hTc hcrit
  obtain ⟨vl, vg, ps, hl, ⟨hlg, h1, h2, h3⟩, -, -⟩ :=
    Work.Chemistry.SRKAcentric.srk_omega1_exists R ac b Tc vc hac hb hv hcr
  have e := iso_7 R ac b Tc hTc
  refine ⟨ps, vl, vg, hl, hlg, ?_, ?_, ?_⟩
  · rw [congrFun e vl]; exact h1
  · rw [congrFun e vg]; exact h2
  · rw [e]; exact h3

/-- The closures have exactly the types of the blind theorems. -/
example : type_of% @closed_srk_acentric = type_of% @Blind.SRKAcentric.srk_acentric := rfl
example : type_of% @closed_srk_exists = type_of% @Blind.SRKAcentric.srk_exists := rfl

end Work.Chemistry.SRKAcentricAudit
