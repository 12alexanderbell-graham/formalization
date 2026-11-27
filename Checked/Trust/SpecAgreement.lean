import Checked.Cosmography.LCDMCoefficients
import Checked.Cosmography.BambaDLy
import Checked.Cosmography.BambaCurved
import Checked.Trust.SecondReadingSpecA
import Checked.Trust.SecondReadingSpecB

/-!
# Blind specification readings agree with pinned definitions (trust track T1/T3, run 2026-11-27T0228Z)

Seven definitions reached by 355 of the 494 pinned definition uses on the claims page (`hubble`,
`decel`, `redshift`, `cosmoCoeff`, `yred`, `omega0`, `lumDistFlat`) were pinned only by specifications
the program wrote (`Checked/Fidelity/*`). Two blind readers (briefs `runs/2026-11-27T0228Z/spec{A,B}/`)
wrote their own specifications from the sources, without the program's text
(`Checked.Trust.SecondReadingSpecA`, `SecondReadingSpecB`). For each definition `X` and reader `R`:

* `meets_X_R : SpecR X` — the program's definition satisfies the reader's specification (so the
  reader's specification is consistent and the program's definition is one of its models);
* `pins_X_R` — every function satisfying the reader's specification equals the program's definition
  on the arguments where the reader says the quantity is determined (the hypotheses of the theorem
  are the reader's own field hypotheses).

Together the two say: an independently written reading of the source determines the same function as
the program's definition on that domain. Where they disagree it is proved:
`not_meets_cosmoCoeff_A` — reader A reads the order-2 coefficient as the deceleration parameter `q`,
the program's `cosmoCoeff 2` is `−q` (its phrase says so; no headline states `cosmoCoeff 2`); the
agreement with reader A holds for `n ≥ 3` (`meets_cosmoCoeff_A_pattern`, `pins_cosmoCoeff_A`).
-/

namespace Checked.Trust.SpecAgreement

open Checked.Cosmography Checked.Cosmography.Aviles Checked.Cosmography.BambaY
open Checked.Cosmography.BambaK Checked.Trust.SecondReadingSpecA Checked.Trust.SecondReadingSpecB

lemma iteratedDeriv_two_eq (a : ℝ → ℝ) (t : ℝ) : iteratedDeriv 2 a t = deriv (deriv a) t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-! ## Hubble rate -/

theorem meets_hubble_A : HubbleSpecA hubble := ⟨fun _ _ _ _ => rfl⟩

theorem pins_hubble_A (H : (ℝ → ℝ) → ℝ → ℝ) (h : HubbleSpecA H) (a : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (hd : DifferentiableAt ℝ a t) : H a t = hubble a t :=
  h.def_formula a t ha hd

theorem meets_hubble_B : HubbleSpecB hubble := ⟨fun _ _ _ _ => rfl⟩

theorem pins_hubble_B (H : (ℝ → ℝ) → ℝ → ℝ) (h : HubbleSpecB H) (a : ℝ → ℝ) (t : ℝ)
    (ha : a t ≠ 0) (hd : DifferentiableAt ℝ a t) : H a t = hubble a t :=
  h.eq_deriv_div a t ha hd

/-! ## Deceleration parameter -/

lemma decel_eq_A (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0) (hd : deriv a t ≠ 0) :
    decel a t = -(iteratedDeriv 2 a t) / (a t * (deriv a t / a t) ^ 2) := by
  unfold decel
  rw [iteratedDeriv_two_eq]
  field_simp

theorem meets_decel_A : DecelSpecA decel :=
  ⟨fun a t ha _ _ hd => decel_eq_A a t ha.ne' hd⟩

theorem pins_decel_A (Q : (ℝ → ℝ) → ℝ → ℝ) (h : DecelSpecA Q) (a : ℝ → ℝ) (t : ℝ)
    (ha : 0 < a t) (h1 : DifferentiableAt ℝ a t) (h2 : DifferentiableAt ℝ (deriv a) t)
    (hd : deriv a t ≠ 0) : Q a t = decel a t := by
  rw [h.def_formula a t ha h1 h2 hd, decel_eq_A a t ha.ne' hd]

theorem meets_decel_B : DecelSpecB decel :=
  ⟨fun a t _ _ _ => by unfold decel; rw [iteratedDeriv_two_eq]⟩

theorem pins_decel_B (Q : (ℝ → ℝ) → ℝ → ℝ) (h : DecelSpecB Q) (a : ℝ → ℝ) (t : ℝ)
    (ha : a t ≠ 0) (h2 : ContDiffAt ℝ 2 a t) (hd : deriv a t ≠ 0) : Q a t = decel a t := by
  rw [h.eq_formula a t ha h2 hd]; unfold decel; rw [iteratedDeriv_two_eq]

/-! ## Redshift -/

theorem meets_redshift_A : RedshiftSpecA redshift := ⟨fun _ _ _ _ _ => rfl⟩

theorem pins_redshift_A (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : RedshiftSpecA Z) (a : ℝ → ℝ) (t₀ t : ℝ)
    (h1 : 0 < a t) (h0 : 0 < a t₀) : Z a t₀ t = redshift a t₀ t :=
  h.def_formula a t₀ t h1 h0

theorem meets_redshift_B : RedshiftSpecB redshift :=
  ⟨fun _ _ _ _ _ _ => by unfold redshift; ring⟩

theorem pins_redshift_B (Z : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : RedshiftSpecB Z) (a : ℝ → ℝ) (t₀ t : ℝ)
    (htt : t ≤ t₀) (h1 : 0 < a t) (h0 : 0 < a t₀) : Z a t₀ t = redshift a t₀ t := by
  have := h.one_add_eq a t₀ t htt h1 h0
  unfold redshift; linarith

/-! ## Cosmographic coefficients -/

/-- The program's `cosmoCoeff` meets reader A's field for every order `n ≥ 3`. -/
theorem meets_cosmoCoeff_A_pattern : ∀ (n : ℕ), 3 ≤ n → ∀ (a : ℝ → ℝ) (t : ℝ), 0 < a t →
    deriv a t ≠ 0 → ContDiffAt ℝ (n : ℕ) a t →
    cosmoCoeff n a t = iteratedDeriv n a t / (a t * (deriv a t / a t) ^ n) :=
  fun _ _ _ _ _ _ _ => rfl

/-- **Disagreement (proved):** reader A's specification is not met by the program's `cosmoCoeff`:
at order 2 reader A reads the deceleration parameter `q`, the program has `−q`. Witness `a = exp`
at `t = 0` (`cosmoCoeff 2 = 1`, reader A's value `−1`). -/
theorem not_meets_cosmoCoeff_A : ¬ CoeffSpecA cosmoCoeff := by
  intro h
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]; simp
  have key := h.decel Real.exp 0 (Real.exp_pos 0) (by rw [Real.deriv_exp]; exact (Real.exp_pos 0).ne')
    Real.contDiff_exp.contDiffAt
  unfold cosmoCoeff hubble at key
  rw [h2, Real.deriv_exp] at key
  norm_num at key

theorem pins_cosmoCoeff_A (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) (h : CoeffSpecA C) (n : ℕ) (hn : 3 ≤ n)
    (a : ℝ → ℝ) (t : ℝ) (ha : 0 < a t) (hd : deriv a t ≠ 0) (hc : ContDiffAt ℝ (n : ℕ) a t) :
    C n a t = cosmoCoeff n a t :=
  h.pattern n hn a t ha hd hc

theorem meets_cosmoCoeff_B : CoeffSpecB cosmoCoeff := ⟨fun _ _ _ _ _ _ _ => rfl⟩

theorem pins_cosmoCoeff_B (C : ℕ → (ℝ → ℝ) → ℝ → ℝ) (h : CoeffSpecB C) (n : ℕ) (a : ℝ → ℝ)
    (t : ℝ) (hn : 3 ≤ n) (ha : a t ≠ 0) (hc : ContDiffAt ℝ (n : ℕ) a t) (hd : deriv a t ≠ 0) :
    C n a t = cosmoCoeff n a t :=
  h.eq_pattern n a t hn ha hc hd

/-! ## y-redshift -/

theorem meets_yred_A : YRedSpecA yred := ⟨fun _ _ _ _ _ => rfl⟩

theorem pins_yred_A (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : YRedSpecA Y) (a : ℝ → ℝ) (t₀ t : ℝ)
    (h1 : 0 < a t) (h0 : 0 < a t₀) : Y a t₀ t = yred a t₀ t :=
  h.def_formula a t₀ t h1 h0

theorem meets_yred_B : YRedSpecB yred where
  eq_one_sub a t₀ t _ h1 h0 := by
    unfold yred redshift
    have e1 := h1.ne'; have e0 := h0.ne'
    rw [show 1 + (a t₀ / a t - 1) = a t₀ / a t by ring]
    field_simp
  eq_z_div _ _ _ _ _ _ := rfl

theorem pins_yred_B (Y : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : YRedSpecB Y) (a : ℝ → ℝ) (t₀ t : ℝ)
    (htt : t ≤ t₀) (h1 : 0 < a t) (h0 : 0 < a t₀) : Y a t₀ t = yred a t₀ t :=
  h.eq_z_div a t₀ t htt h1 h0

/-! ## Present density parameter -/

theorem meets_omega0_A : Omega0SpecA omega0 :=
  ⟨fun _ _ _ _ _ _ => by unfold omega0 hubble; ring⟩

theorem pins_omega0_A (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : Omega0SpecA O) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : 0 < a t₀) (hd : DifferentiableAt ℝ a t₀) (hH : deriv a t₀ ≠ 0) :
    O K a t₀ = omega0 K a t₀ := by
  rw [h.def_formula K a t₀ ha hd hH]; unfold omega0 hubble; ring

theorem meets_omega0_B : Omega0SpecB omega0 :=
  ⟨fun _ _ _ _ _ _ => by unfold omega0 hubble; ring⟩

theorem pins_omega0_B (O : ℝ → (ℝ → ℝ) → ℝ → ℝ) (h : Omega0SpecB O) (K : ℝ) (a : ℝ → ℝ) (t₀ : ℝ)
    (ha : a t₀ ≠ 0) (hd : DifferentiableAt ℝ a t₀) (hH : deriv a t₀ ≠ 0) :
    O K a t₀ = omega0 K a t₀ := by
  rw [h.eq_friedmann K a t₀ ha hd hH]; unfold omega0 hubble; ring

/-! ## Flat luminosity distance -/

theorem meets_lumDistFlat_A : LumDistFlatSpecA lumDistFlat :=
  ⟨fun _ _ _ _ _ _ => by unfold lumDistFlat redshift comoving; ring⟩

theorem pins_lumDistFlat_A (D : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistFlatSpecA D) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hc : ContinuousOn a (Set.Icc t t₀))
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) : D a t₀ t = lumDistFlat a t₀ t := by
  rw [h.def_formula a t₀ t htt hc hpos]; unfold lumDistFlat redshift comoving; ring

theorem meets_lumDistFlat_B : LumDistFlatSpecB lumDistFlat :=
  ⟨fun _ _ _ _ _ _ => by unfold lumDistFlat redshift comoving; ring⟩

theorem pins_lumDistFlat_B (D : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : LumDistFlatSpecB D) (a : ℝ → ℝ)
    (t₀ t : ℝ) (htt : t ≤ t₀) (hc : ContinuousOn a (Set.Icc t t₀))
    (hpos : ∀ s ∈ Set.Icc t t₀, 0 < a s) : D a t₀ t = lumDistFlat a t₀ t := by
  rw [h.eq_integral a t₀ t htt hc hpos]; unfold lumDistFlat redshift comoving; ring

end Checked.Trust.SpecAgreement
