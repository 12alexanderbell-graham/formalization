import Mathlib
import Checked.Data.Moresco16Min
import Work.Data.Moresco16MinBlind
import Work.Data.Moresco16BlindClosed

/-!
# Audit of the promoted Moresco 2016 headlines (run 2026-11-05T1028Z)

The Checked copies (`Checked/Data/Moresco16*.lean`, promoted by
`runs/2026-11-05T1028Z/scripts/promote_m16.py`) state the same claims about the same objects as the
frozen Work statements, and the blind restatement of run 2026-11-05T0628Z
(`Work/Data/Moresco16MinBlind.lean`, a different model, from the paper alone) follows from the
CHECKED headline `Checked.Data.Moresco16Min.chiSqOL_ge`, not from the Work proof:
* `work_eq_*`: each Work definition equals its Checked copy (definitional);
* `chi2_ge`, `claimA`, `claimB`: the blind claims, statements identical to the blind file, proved
  through the Checked headline (proof copied from `Work/Data/Moresco16MinBlindClosed.lean` with the
  Work headline replaced).
-/

namespace Work.Data.Moresco16PromotionAudit
open Work.Data.Moresco16MinBlind
open Checked.Data.Moresco16

theorem work_eq_m16Table : Work.Data.Moresco16.m16Table = Checked.Data.Moresco16.m16Table := rfl
theorem work_eq_e2OL : Work.Data.Moresco16.e2OL = Checked.Data.Moresco16.e2OL := rfl
theorem work_eq_chiSqOL : Work.Data.Moresco16.chiSqOL = Checked.Data.Moresco16.chiSqOL := rfl
theorem work_eq_chiSqLine : Work.Data.Moresco16.chiSqLine = Checked.Data.Moresco16.chiSqLine := rfl

theorem data (i : Fin 30) : zD i = (m16Table i).1 ∧ HD i = (m16Table i).2.1 ∧
    sD i = (m16Table i).2.2 := by
  fin_cases i <;> norm_num [zD, HD, sD, m16Table]

theorem chi2_eq (p : ℝ × ℝ × ℝ) : chi2 p = chiSqOL p.1 p.2.1 (OL p.2.1 p.2.2) := by
  unfold chi2 chiSqOL
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨hz, hH, hs⟩ := data i
    rw [hz, hH, hs, div_pow]
    unfold E2 e2OL
    ring
  · ring

theorem valid_wide (p : ℝ × ℝ × ℝ) (hp : Valid p) :
    p.2.1 ≤ 1 ∧ 0 ≤ OL p.2.1 p.2.2 ∧ ∀ i, 0 ≤ e2OL p.2.1 (OL p.2.1 p.2.2) (m16Table i).1 := by
  obtain ⟨_, h1, h2, h3, _, h5⟩ := hp
  refine ⟨h2, by unfold OL; positivity, fun i => ?_⟩
  have := h5 i
  rw [(data i).1] at this
  exact this.le

theorem chi2_ge (p : ℝ × ℝ × ℝ) (hp : Valid p) : 14.9665 ≤ chi2 p := by
  obtain ⟨a, b, c⟩ := valid_wide p hp
  rw [chi2_eq]
  exact Checked.Data.Moresco16Min.chiSqOL_ge _ _ _ a b c

theorem claimA :
    (chi2 '' {p | Valid p}).Nonempty ∧
    ∃ L : ℝ, IsGLB (chi2 '' {p | Valid p}) L ∧ |L - 14.967| ≤ 0.0005 := by
  set p0 : ℝ × ℝ × ℝ := (72.2865, 0.43617, 0.651)
  have hv : Valid p0 := by
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, fun i => ?_⟩
    fin_cases i <;> norm_num [E2, OL, zD, p0]
  have hc : chi2 p0 < 14.9675 := by
    have hterm : ∀ i, ((HD i - p0.1 * Real.sqrt (E2 p0.2.1 p0.2.2 (zD i))) / sD i) ^ 2 ≤
        Work.Data.Moresco16Certs.cUb i := by
      intro i
      have h := Work.Data.Moresco16BlindClosed.term_bound_b i
      rw [← Work.Data.Moresco16BlindClosed.table4_second_reading, work_eq_m16Table] at h
      obtain ⟨hz, hH, hs⟩ := data i
      rw [hz, hH, hs]
      simpa [E2, OL, p0] using h
    unfold chi2
    have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
    have hU : (∑ i, Work.Data.Moresco16Certs.cUb i) + ((72.2865 - 73) / 2.4) ^ 2 <
        (14.9675 : ℝ) := by
      simp only [Work.Data.Moresco16Certs.cUb, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      norm_num
    simp only [p0] at hs ⊢
    linarith
  have hmem : chi2 p0 ∈ chi2 '' {p | Valid p} := ⟨p0, hv, rfl⟩
  have hlow : ∀ x ∈ chi2 '' {p | Valid p}, 14.9665 ≤ x := by
    rintro x ⟨p, hp, rfl⟩; exact chi2_ge p hp
  have hne : (chi2 '' {p | Valid p}).Nonempty := ⟨_, hmem⟩
  have hbdd : BddBelow (chi2 '' {p | Valid p}) := ⟨14.9665, hlow⟩
  refine ⟨hne, sInf _, isGLB_csInf hne hbdd, ?_⟩
  have h1 := le_csInf hne hlow
  have h2 := csInf_le hbdd hmem
  rw [abs_le]; constructor <;> linarith

theorem claimB :
    ∀ p, Valid p → ∀ N : ℕ, 5 ≤ N → N ≤ 50 →
      0.005 < |AICc (chi2 p) 3 N - 21.41| := by
  intro p hp N hN5 hN50
  have hc := chi2_ge p hp
  have h5 : (5 : ℝ) ≤ N := by exact_mod_cast hN5
  have h50 : (N : ℝ) ≤ 50 := by exact_mod_cast hN50
  have hq : (24 : ℝ) / 46 ≤ 24 / ((N : ℝ) - 3 - 1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  unfold AICc
  rw [lt_abs]; left
  push_cast
  have : (2 : ℝ) * 3 * (3 + 1) / ((N : ℝ) - 3 - 1) = 24 / ((N : ℝ) - 3 - 1) := by norm_num
  rw [this]
  norm_num at hq ⊢
  linarith

end Work.Data.Moresco16PromotionAudit

#print axioms Work.Data.Moresco16PromotionAudit.work_eq_chiSqOL
#print axioms Work.Data.Moresco16PromotionAudit.claimA
#print axioms Work.Data.Moresco16PromotionAudit.claimB
