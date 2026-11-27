import Checked.Cosmography.FRCosmo
import Checked.Cosmography.BambaZ
import Checked.Cosmography.CPLCoefficients
import Checked.Cosmography.LCDMCoefficients
import Checked.Trust.SecondReadingSpecG
import Checked.Trust.SecondReadingSpecH
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

/-!
# Sourced blind specification readings G and H against four pinned definitions (run 2026-11-27T0428Z)

Same theorem names and shapes as `Checked/Trust/SpecAgreementCD.lean`: `meets_X_R : SpecR X` (the program's
definition is a model of reader R's specification) and `pins_X_R` (every function or condition meeting R's
specification equals / is equivalent to the program's, on R's domain), or `not_meets_X_R` with a witness.
Unlike readers C and D (run 2026-11-27T0228Z, memory only), readers G (Sonnet) and H (Opus) were handed
verbatim LaTeX excerpts of the three sources (`runs/2026-11-27T0428Z/sources/`).

Results:
* `curv` (Ricci scalar, Bamba et al. 2012 §XI): G and H AGREE (`meets_curv_G/H`, `pins_curv_G/H`). Both
  readers found the source's own inconsistency: §VIII.C writes `R = 6(Ḣ + 2H²)`, §XI (11.6) `R = −6(Ḣ + 2H²)`
  for the same metric; readers C and D (memory) had the §VIII sign.
* `curvK`: G AGREES; H DISAGREES (H reads the parameter as `Ω_K = −K/(H₀²a₀²)`, §X's named density
  parameter; the program's is the ratio `K/(H₀²a₀²)` printed in the coefficients, `= Ω₀ − 1`):
  `not_meets_curvK_H`, and H's specification determines minus the program's (`pins_neg_curvK_H`).
* `IsFlatLCDM`, `IsFlatCPL`: G AGREES for every argument (G, like the program, requires expansion at `t₀` and
  the law near `t₀`). H DISAGREES on contracting universes only (H does not require `H₀ > 0`; the
  contracting de Sitter universe meets H's condition, not the program's); H's condition is equivalent to the
  program's wherever `H₀ > 0` (`pins_IsFlatLCDM_H`, `pins_IsFlatCPL_H`). Both sourced readers read the law as
  holding near `t₀`, as the program does (reader D's all-times reading is not reproduced with the source).
-/

namespace Checked.Trust.SpecAgreement

open Filter Topology Real Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.BambaZ
open Checked.Cosmography.CPL Checked.Cosmography.FRCosmo
open Checked.Trust.SecondReadingSpecG Checked.Trust.SecondReadingSpecH

/-! ## Ricci scalar (§XI sign): both sourced readers agree -/

theorem meets_curv_G : RicciFlatSpecG curv :=
  ⟨fun _ _ _ _ _ => rfl⟩

theorem pins_curv_G (R : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatSpecG R) (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0)
    (h1 : ∀ᶠ s in nhds t, DifferentiableAt ℝ a s) (h2 : DifferentiableAt ℝ (deriv a) t) :
    R a t = curv a t := by
  rw [h.formula a t ha h1 h2, meets_curv_G.formula a t ha h1 h2]

theorem meets_curv_H : RicciFlatSpecH curv :=
  ⟨fun _ _ _ _ _ => rfl⟩

theorem pins_curv_H (R : (ℝ → ℝ) → ℝ → ℝ) (h : RicciFlatSpecH R) (a : ℝ → ℝ) (t : ℝ) (ha : 0 < a t)
    (h1 : ∀ᶠ s in nhds t, DifferentiableAt ℝ a s) (h2 : DifferentiableAt ℝ (deriv a) t) :
    R a t = curv a t := by
  rw [h.formula a t ha h1 h2, meets_curv_H.formula a t ha h1 h2]

/-! ## Curvature parameter -/

theorem meets_curvK_G : CurvParamSpecG curvK :=
  ⟨fun K a t₀ _ _ => by unfold curvK Checked.Cosmography.hubble; ring⟩

theorem pins_curvK_G (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvParamSpecG k) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : a t₀ ≠ 0) (hd : deriv a t₀ ≠ 0) : k K a t₀ = curvK K a t₀ := by
  rw [h.formula K a t₀ ha hd, meets_curvK_G.formula K a t₀ ha hd]

/-- **Disagreement (proved):** for `K = 1`, `a = exp`, `t₀ = 0` the program's parameter is `1`, reader H's `−1`. -/
theorem not_meets_curvK_H : ¬ CurvParamSpecH curvK := by
  intro h
  have e := h.formula 1 Real.exp 0 (Real.exp_pos 0) (by rw [Real.deriv_exp]; exact (Real.exp_pos 0).ne')
  unfold curvK Checked.Cosmography.hubble at e
  rw [Real.deriv_exp] at e
  have h0 : Real.exp 0 ≠ 0 := (Real.exp_pos 0).ne'
  field_simp at e
  norm_num at e

/-- Reader H's specification determines minus the program's curvature parameter. -/
theorem pins_neg_curvK_H (k : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : CurvParamSpecH k) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : 0 < a t₀) (hd : deriv a t₀ ≠ 0) : k K a t₀ = -curvK K a t₀ := by
  rw [h.formula K a t₀ ha hd]
  unfold curvK Checked.Cosmography.hubble
  ring

/-! ## Flat ΛCDM and flat CPL model conditions -/

lemma lcdm_radicand (Ω x : ℝ) : Ω * (1 + (x - 1)) ^ 3 + 1 - Ω = Ω * x ^ 3 + (1 - Ω) := by ring

theorem meets_IsFlatLCDM_G : FlatLCDMSpecG IsFlatLCDM := by
  refine ⟨fun Ω a t₀ => ?_⟩
  unfold IsFlatLCDM redshift
  simp only [Checked.Cosmography.hubble, Checked.Trust.SecondReadingSpecG.hubble, lcdm_radicand]
  constructor
  · rintro ⟨hH, ev⟩
    exact ⟨ev.self_of_nhds.1, hH, ev⟩
  · rintro ⟨_, hH, ev⟩
    exact ⟨hH, ev⟩

theorem pins_IsFlatLCDM_G (P : ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatLCDMSpecG P) (Ω : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) : P Ω a t₀ ↔ IsFlatLCDM Ω a t₀ := by
  rw [h.iff, meets_IsFlatLCDM_G.iff]

lemma cpl_radicand (Ω w₀ wₐ : ℝ) (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Ω * (1 + (y / x - 1)) ^ 3 + (1 - Ω) * (1 + (y / x - 1)) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * (y / x - 1)) / (1 + (y / x - 1))) =
    Ω * (y / x) ^ (3 : ℝ) + (1 - Ω) * (y / x) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-3 * wₐ * (1 - x / y)) := by
  rw [show 1 + (y / x - 1) = y / x by ring, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  congr 3
  field_simp

theorem meets_IsFlatCPL_G : FlatCPLSpecG IsFlatCPL := by
  refine ⟨fun Ω w₀ wₐ a t₀ => ?_⟩
  unfold IsFlatCPL redshift
  simp only [Checked.Cosmography.hubble, Checked.Trust.SecondReadingSpecG.hubble]
  constructor
  · rintro ⟨hH, ev⟩
    have h0 := ev.self_of_nhds.1
    exact ⟨h0, hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by
      rw [q, cpl_radicand Ω w₀ wₐ (a t) (a t₀) p.ne' h0.ne']⟩⟩
  · rintro ⟨h0, hH, ev⟩
    exact ⟨hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by
      rw [q, cpl_radicand Ω w₀ wₐ (a t) (a t₀) p.ne' h0.ne']⟩⟩

theorem pins_IsFlatCPL_G (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatCPLSpecG P) (Ω w₀ wₐ : ℝ)
    (a : ℝ → ℝ) (t₀ : ℝ) : P Ω w₀ wₐ a t₀ ↔ IsFlatCPL Ω w₀ wₐ a t₀ := by
  rw [h.iff, meets_IsFlatCPL_G.iff]

/-! Reader H: the law written as `HasDerivAt a (a t * (H₀ * √…)) t` near `t₀`, no sign condition on `H₀`. -/

/-- Generic bridge: near `t₀`, "`a` has derivative `a t * (H₀ * F t)`" is "`a > 0`, differentiable, and
`a'/a = H₀ * F t`", given `a t₀ > 0`. -/
lemma hasDeriv_iff_hubble (a F : ℝ → ℝ) (t₀ H₀ : ℝ) (ha : 0 < a t₀) :
    (∀ᶠ t in nhds t₀, HasDerivAt a (a t * (H₀ * F t)) t) ↔
      ∀ᶠ t in nhds t₀, 0 < a t ∧ DifferentiableAt ℝ a t ∧ deriv a t / a t = H₀ * F t := by
  constructor
  · intro ev
    have hc : ContinuousAt a t₀ := ev.self_of_nhds.continuousAt
    have hpos : ∀ᶠ t in nhds t₀, 0 < a t := hc.eventually (lt_mem_nhds ha)
    filter_upwards [ev, hpos] with t hd hp
    refine ⟨hp, hd.differentiableAt, ?_⟩
    rw [hd.deriv]
    field_simp
  · intro ev
    filter_upwards [ev] with t ⟨hp, hd, hq⟩
    have : deriv a t = a t * (H₀ * F t) := by
      rw [← hq]; field_simp
    rw [← this]
    exact hd.hasDerivAt

lemma hasDerivAt_expNeg' (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
  have := (hasDerivAt_neg t).exp
  convert this using 1; ring

lemma hubble_expNeg' (t : ℝ) : deriv (fun s => Real.exp (-s)) t / Real.exp (-t) = -1 := by
  rw [(hasDerivAt_expNeg' t).deriv]; field_simp

/-- **Disagreement (proved):** the contracting de Sitter universe `a = e^{−t}`, `Ω = 0`, meets reader H's flat
ΛCDM condition at `t₀ = 0`, not the program's (which requires expansion at `t₀`). -/
theorem not_meets_IsFlatLCDM_H : ¬ FlatLCDMSpecH IsFlatLCDM := by
  intro h
  have hd : deriv (fun s => Real.exp (-s)) 0 ≠ 0 := by
    rw [(hasDerivAt_expNeg' 0).deriv]; simp
  have hc := (h.iff 0 (fun s => Real.exp (-s)) 0 (Real.exp_pos _) hd).2 (Eventually.of_forall fun t => by
    have e : Real.exp (-t) * (deriv (fun s => Real.exp (-s)) 0 / Real.exp (-0) *
        Real.sqrt (0 * (Real.exp (-0) / Real.exp (-t)) ^ (3 : ℕ) + 1 - 0)) = -Real.exp (-t) := by
      rw [hubble_expNeg']; simp
    rw [e]; exact hasDerivAt_expNeg' t)
  have := hc.1
  unfold Checked.Cosmography.hubble at this
  rw [hubble_expNeg'] at this
  norm_num at this

theorem pins_IsFlatLCDM_H (P : ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatLCDMSpecH P) (Ω : ℝ) (a : ℝ → ℝ)
    (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < deriv a t₀ / a t₀) : P Ω a t₀ ↔ IsFlatLCDM Ω a t₀ := by
  have hd : deriv a t₀ ≠ 0 := fun e => by rw [e, zero_div] at hH; exact lt_irrefl 0 hH
  rw [h.iff Ω a t₀ ha hd, hasDeriv_iff_hubble a _ t₀ _ ha]
  unfold IsFlatLCDM redshift
  simp only [Checked.Cosmography.hubble, lcdm_radicand]
  constructor
  · intro ev
    exact ⟨hH, ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [q]; ring_nf⟩⟩
  · rintro ⟨_, ev⟩
    exact ev.mono fun t ⟨p, d, q⟩ => ⟨p, d, by rw [q]; ring_nf⟩

/-- **Disagreement (proved):** the same contracting universe (`Ω = 0`, `w₀ = −1`, `wₐ = 0`) meets reader H's
flat CPL condition, not the program's. -/
theorem not_meets_IsFlatCPL_H : ¬ FlatCPLSpecH IsFlatCPL := by
  intro h
  have hd : deriv (fun s => Real.exp (-s)) 0 ≠ 0 := by
    rw [(hasDerivAt_expNeg' 0).deriv]; simp
  have hc := (h.iff 0 (-1) 0 (fun s => Real.exp (-s)) 0 (Real.exp_pos _) hd).2
    (Eventually.of_forall fun t => by
      have e : Real.exp (-t) * (deriv (fun s => Real.exp (-s)) 0 / Real.exp (-0) *
          Real.sqrt (0 * (Real.exp (-0) / Real.exp (-t)) ^ (3 : ℕ) + (1 - 0) *
            (Real.exp (-0) / Real.exp (-t)) ^ (3 * (1 + (-1) + 0) : ℝ) *
              Real.exp (-(3 * 0 * (Real.exp (-0) / Real.exp (-t) - 1)) /
                (Real.exp (-0) / Real.exp (-t))))) = -Real.exp (-t) := by
        rw [hubble_expNeg']; norm_num
      rw [e]; exact hasDerivAt_expNeg' t)
  have := hc.1
  unfold Checked.Cosmography.hubble at this
  rw [hubble_expNeg'] at this
  norm_num at this

lemma cpl_radicand_H (Ω w₀ wₐ : ℝ) (x y : ℝ) :
    Ω * (1 + (y / x - 1)) ^ 3 + (1 - Ω) * (1 + (y / x - 1)) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * (y / x - 1)) / (1 + (y / x - 1))) =
    Ω * (y / x) ^ (3 : ℕ) + (1 - Ω) * (y / x) ^ (3 * (1 + w₀ + wₐ)) *
      Real.exp (-(3 * wₐ * (y / x - 1)) / (y / x)) := by
  rw [show 1 + (y / x - 1) = y / x by ring]

theorem pins_IsFlatCPL_H (P : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → Prop) (h : FlatCPLSpecH P) (Ω w₀ wₐ : ℝ)
    (a : ℝ → ℝ) (t₀ : ℝ) (ha : 0 < a t₀) (hH : 0 < deriv a t₀ / a t₀) :
    P Ω w₀ wₐ a t₀ ↔ IsFlatCPL Ω w₀ wₐ a t₀ := by
  have hd : deriv a t₀ ≠ 0 := fun e => by rw [e, zero_div] at hH; exact lt_irrefl 0 hH
  rw [h.iff Ω w₀ wₐ a t₀ ha hd, hasDeriv_iff_hubble a _ t₀ _ ha]
  unfold IsFlatCPL redshift
  simp only [Checked.Cosmography.hubble, cpl_radicand_H]
  constructor
  · intro ev
    exact ⟨hH, ev⟩
  · rintro ⟨_, ev⟩
    exact ev

end Checked.Trust.SpecAgreement
