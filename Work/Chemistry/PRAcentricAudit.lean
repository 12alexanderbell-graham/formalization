import Mathlib
import Work.Chemistry.PRAcentric
import Work.Chemistry.PRAcentricBlind

/-!
# Audit (run 2026-11-05T1228Z): the blind restatement of the PR ω = 1 claim, closed

`Work/Chemistry/PRAcentricBlind.lean` was written by a blind restater (Sonnet) from the claim in
words only (notes `runs/2026-11-05T1228Z/blind/notes_pr.md`). Its three theorems are proved here
from the frozen headlines `Work.Chemistry.PRAcentric.pr_omega1_unique` and `pr_omega1_exists`.
-/

namespace Work.Chemistry.PRAcentricAudit
open Checked.Records Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence Blind.PRAcentric

lemma iso_c (R b ac κ Tc : ℝ) (hTc : 0 < Tc) :
    (fun v => prP R b ac κ Tc v Tc) = cubicP R ac b 2 (-1) Tc := by
  funext v
  have : Tc / Tc = 1 := div_self hTc.ne'
  simp only [prP, aT, cubicP, this, Real.sqrt_one, sub_self, mul_zero, add_zero, one_pow, mul_one]
  ring_nf

lemma iso_7 (R b ac Tc : ℝ) (hTc : 0 < Tc) :
    (fun v => prP R b ac (kappa 1) Tc v (7 / 10 * Tc)) =
      cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
        b 2 (-1) (7 / 10 * Tc) := by
  funext v
  have : 7 / 10 * Tc / Tc = 7 / 10 := by field_simp
  simp only [prP, aT, cubicP, kappa, this]
  ring_nf

lemma crit (R b ac Tc vc Pc : ℝ) (hc : IsCriticalPoint R b ac (kappa 1) Tc vc Pc) :
    0 < Tc ∧ b < vc ∧ IsCriticalIsotherm (cubicP R ac b 2 (-1) Tc) vc ∧
      Pc = cubicP R ac b 2 (-1) Tc vc := by
  obtain ⟨hT, hv, h1, h2, hP⟩ := hc
  rw [iso_c R b ac (kappa 1) Tc hT] at h1 h2
  refine ⟨hT, hv, ⟨h1, h2⟩, ?_⟩
  rw [hP]; exact congrFun (iso_c R b ac (kappa 1) Tc hT) vc

lemma coex (R b ac Tc vl vg ps : ℝ) (hTc : 0 < Tc)
    (h : IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps) :
    b < vl ∧ IsMaxwellCoexistence
      (cubicP R (ac * (1 + (0.37464 + 1.54226 * 1 - 0.26992 * 1 ^ 2) * (1 - Real.sqrt (7 / 10))) ^ 2)
        b 2 (-1) (7 / 10 * Tc)) vl vg ps := by
  obtain ⟨hl, hlg, h1, h2, h3⟩ := h
  have e := iso_7 R b ac Tc hTc
  refine ⟨hl, hlg, ?_, ?_, ?_⟩
  · rw [← congrFun e vl]; exact h1
  · rw [← congrFun e vg]; exact h2
  · rw [← e]; exact h3

theorem closed_numbers (R b ac : ℝ) (hR : 0 < R) (hb : 0 < b) (hac : 0 < ac)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R b ac (kappa 1) Tc vc Pc)
    (vl vg ps : ℝ) (hco : IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps) :
    0 < ps / Pc ∧
    Checked.Records.RoundsTo (ps / Pc) (114 / 10000) 4 ∧
    Checked.Records.RoundsTo (Blind.PRAcentric.acentric ps Pc) (942 / 1000) 3 ∧
    Blind.PRAcentric.acentric ps Pc ≠ 1 := by
  obtain ⟨hT, hv, hcr, hP⟩ := crit R b ac Tc vc Pc hc
  obtain ⟨hl, hM⟩ := coex R b ac Tc vl vg ps hT hco
  obtain ⟨r1, r2⟩ := Work.Chemistry.PRAcentric.pr_omega1_unique R ac b Tc vc vl vg ps hac hb hv hcr hl hM
  rw [← hP] at r1 r2
  have e : Blind.PRAcentric.acentric ps Pc = Checked.Chemistry.Coexistence.acentric ps Pc := rfl
  unfold RoundsTo at r1 r2 ⊢
  rw [abs_le] at r1 r2
  rw [e]
  refine ⟨by norm_num at r1; linarith [r1.1], ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> norm_num at r1 ⊢ <;> linarith [r1.1, r1.2]
  · rw [abs_le]; constructor <;> norm_num at r2 ⊢ <;> linarith [r2.1, r2.2]
  · intro h1; rw [h1] at r2; norm_num at r2

theorem closed_exists (R b ac : ℝ) (hR : 0 < R) (hb : 0 < b) (hac : 0 < ac)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R b ac (kappa 1) Tc vc Pc) :
    ∃ vl vg ps, IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps := by
  obtain ⟨hT, hv, hcr, -⟩ := crit R b ac Tc vc Pc hc
  obtain ⟨vl, vg, ps, hl, ⟨hlg, h1, h2, h3⟩, -⟩ :=
    Work.Chemistry.PRAcentric.pr_omega1_exists R ac b Tc vc hac hb hv hcr
  have e := iso_7 R b ac Tc hT
  refine ⟨vl, vg, ps, hl, hlg, ?_, ?_, ?_⟩
  · rw [congrFun e vl]; exact h1
  · rw [congrFun e vg]; exact h2
  · rw [e]; exact h3

theorem closed_pr_acentric (R b ac : ℝ) (hR : 0 < R) (hb : 0 < b) (hac : 0 < ac)
    (Tc vc Pc : ℝ) (hc : IsCriticalPoint R b ac (kappa 1) Tc vc Pc) :
    (∃ vl vg ps, IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps) ∧
    ∀ vl vg ps, IsCoexistence R b ac (kappa 1) Tc (7 / 10 * Tc) vl vg ps →
      0 < ps / Pc ∧
      Checked.Records.RoundsTo (ps / Pc) (114 / 10000) 4 ∧
      Checked.Records.RoundsTo (Blind.PRAcentric.acentric ps Pc) (942 / 1000) 3 ∧
      Blind.PRAcentric.acentric ps Pc ≠ 1 :=
  ⟨closed_exists R b ac hR hb hac Tc vc Pc hc,
    fun vl vg ps h => closed_numbers R b ac hR hb hac Tc vc Pc hc vl vg ps h⟩

end Work.Chemistry.PRAcentricAudit
