import Work.Cosmography.B1Blind
import Checked.Cosmography.B1Truncation

/-!
# B1 fidelity audit (run 2026-10-31T0428Z): the blind restatement closed in Lean

`Work/Cosmography/B1Blind.lean` was written by a subagent from the informal claims only (no
access to the frozen file). Here each blind statement is derived from the program's frozen
theorems (`Checked.Cosmography.B1`). The blind model `FlatLCDMOn` bundles the same hypotheses;
the blind log-polynomial is `ln 10 · (1/H₀) · (…)` (ours: `ln 10 / H₀ · (…)`); thresholds are
decimals (`0.09`, `0.3`, `0.18`); the blind shape claim does not assume `t₇ ≤ t₃` (derived here
from the model: `a` increases on `[t₃, t₀]`).
-/

namespace Work.Cosmography.B1Audit

open Checked.Cosmography Checked.Cosmography.BambaY Work.Cosmography.B1Blind

lemma poly_eq (H Ω z : ℝ) :
    logPolyLCDM H Ω z = Checked.Cosmography.B1.logPolyDL3 (Checked.Cosmography.B1.lusA2 Ω)
      (Checked.Cosmography.B1.lusA3 Ω) H z := by
  unfold logPolyLCDM logPoly coeffA2 coeffA3 logx Checked.Cosmography.B1.logPolyDL3
    Checked.Cosmography.B1.lusA2 Checked.Cosmography.B1.lusA3
  ring

lemma omega_bounds (Ω : ℝ) (hΩ : Ω ∈ Set.Icc (0.2 : ℝ) 0.4) : 1 / 5 ≤ Ω ∧ Ω ≤ 2 / 5 := by
  obtain ⟨h1, h2⟩ := hΩ; constructor <;> norm_num at h1 h2 ⊢ <;> linarith

theorem blind_lumDist (a : ℝ → ℝ) (Ω t t₀ : ℝ) (hΩ0 : 0 ≤ Ω) (hΩ1 : Ω ≤ 1)
    (hM : FlatLCDMOn a Ω t t₀) :
    lumDistFlat a t₀ t =
      (1 + redshift a t₀ t) / hubble a t₀ *
        ∫ v in Real.sqrt (a t / a t₀)..1, 2 / Real.sqrt (Ω + (1 - Ω) * v ^ 6) :=
  Checked.Cosmography.B1.lumDistFlat_flatLCDM Ω hΩ0 hΩ1 a t t₀ hM.le hM.pos hM.diff hM.H0_pos
    hM.friedmann

theorem blind_z3 (a : ℝ → ℝ) (Ω t t₀ : ℝ) (hΩ : Ω ∈ Set.Icc (0.2 : ℝ) 0.4)
    (hM : FlatLCDMOn a Ω t t₀) (hz : redshift a t₀ t = 3) :
    0 < logPolyLCDM (hubble a t₀) Ω (redshift a t₀ t) ∧ 0.09 < deltaMu a Ω t₀ t := by
  obtain ⟨h1, h2⟩ := omega_bounds Ω hΩ
  obtain ⟨hp, hm⟩ := Checked.Cosmography.B1.cubic_misses_z3 Ω h1 h2 a t t₀ hM.le hM.pos hM.diff
    hM.H0_pos hM.friedmann hz
  unfold deltaMu; simp only [poly_eq]
  exact ⟨hp, by norm_num; linarith⟩

theorem blind_z7 (a : ℝ → ℝ) (Ω t t₀ : ℝ) (hΩ : Ω ∈ Set.Icc (0.2 : ℝ) 0.4)
    (hM : FlatLCDMOn a Ω t t₀) (hz : redshift a t₀ t = 7) :
    0 < logPolyLCDM (hubble a t₀) Ω (redshift a t₀ t) ∧ 0.3 < deltaMu a Ω t₀ t := by
  obtain ⟨h1, h2⟩ := omega_bounds Ω hΩ
  obtain ⟨hp, hm⟩ := Checked.Cosmography.B1.cubic_misses_z7 Ω h1 h2 a t t₀ hM.le hM.pos hM.diff
    hM.H0_pos hM.friedmann hz
  unfold deltaMu; simp only [poly_eq]
  exact ⟨hp, by norm_num; linarith⟩

/-- In the model, `a` is strictly increasing on `[t, t₀]` (`H > 0` there). -/
lemma strictMono_of_model (a : ℝ → ℝ) (Ω t t₀ : ℝ) (hΩ : Ω ≤ 2 / 5) (hΩ0 : 0 ≤ Ω)
    (hM : FlatLCDMOn a Ω t t₀) : StrictMonoOn a (Set.Icc t t₀) := by
  have ha₀ : 0 < a t₀ := hM.pos t₀ ⟨hM.le, le_rfl⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc t t₀)
  · intro x hx; exact (hM.diff x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxI : x ∈ Set.Icc t t₀ := ⟨hx.1.le, hx.2.le⟩
    have hax := hM.pos x hxI
    have hf := hM.friedmann x hxI
    unfold hubble at hf
    have harg : 0 < Ω * (1 + redshift a t₀ x) ^ 3 + 1 - Ω := by
      have : 0 ≤ Ω * (1 + redshift a t₀ x) ^ 3 := by
        unfold redshift
        exact mul_nonneg hΩ0 (pow_nonneg (by rw [add_sub_cancel]; positivity) 3)
      linarith
    have hpos : 0 < deriv a t₀ / a t₀ * √(Ω * (1 + redshift a t₀ x) ^ 3 + 1 - Ω) :=
      mul_pos (by have := hM.H0_pos; unfold hubble at this; exact this) (Real.sqrt_pos.2 harg)
    rw [← hf] at hpos
    exact (div_pos_iff_of_pos_right hax).1 hpos

theorem blind_diff (a : ℝ → ℝ) (Ω t₃ t₇ t₀ : ℝ) (hΩ : Ω ∈ Set.Icc (0.2 : ℝ) 0.4)
    (hM₃ : FlatLCDMOn a Ω t₃ t₀) (hM₇ : FlatLCDMOn a Ω t₇ t₀)
    (hz₃ : redshift a t₀ t₃ = 3) (hz₇ : redshift a t₀ t₇ = 7) :
    0.18 < deltaMu a Ω t₀ t₇ - deltaMu a Ω t₀ t₃ := by
  obtain ⟨h1, h2⟩ := omega_bounds Ω hΩ
  have h73 : t₇ ≤ t₃ := by
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have hmono := strictMono_of_model a Ω t₃ t₀ h2 (by linarith) hM₃
    have hlt' := hmono ⟨le_rfl, hM₃.le⟩ ⟨hlt.le, hM₇.le⟩ hlt
    have ha₀ : 0 < a t₀ := hM₃.pos t₀ ⟨hM₃.le, le_rfl⟩
    have ha3 : 0 < a t₃ := hM₃.pos t₃ ⟨le_rfl, hM₃.le⟩
    have ha7 : 0 < a t₇ := hM₇.pos t₇ ⟨le_rfl, hM₇.le⟩
    unfold redshift at hz₃ hz₇
    have e3 : a t₀ = 4 * a t₃ := by field_simp at hz₃; linarith
    have e7 : a t₀ = 8 * a t₇ := by field_simp at hz₇; linarith
    linarith
  have hm := Checked.Cosmography.B1.cubic_shape_miss Ω h1 h2 a t₇ t₃ t₀ h73 hM₃.le hM₇.pos
    hM₇.diff hM₇.H0_pos hM₇.friedmann hz₃ hz₇
  unfold deltaMu; simp only [poly_eq]
  norm_num; linarith

end Work.Cosmography.B1Audit
