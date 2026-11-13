import Checked.Trust.NonVacuity
import Checked.Fidelity.Pins
import Checked.Fidelity.FlatPins

/-! Hypothesis necessity for the distance pinning theorems: the luminosity and angular-diameter distance specifications constrain their function only on the admissible domain (emission before observation, a positive and continuous scale factor in between), and both are invariant under rescaling and time translation, which keep that domain; so the program's distances shifted by one off the domain still meet the specifications, and each domain condition is needed (a later emission time, a negative or zero scale factor, a scale factor with a jump). Module `NecessityU`. -/

namespace Checked.Trust.NCV

open Set Checked.Cosmography Checked.Cosmography.BambaY Checked.Cosmography.BambaK
open Checked.Cosmography.BambaA Checked.Cosmography.Transverse Checked.Fidelity

/-- The admissible domain of the distance specifications. -/
def Dom (a : ℝ → ℝ) (t₀ t : ℝ) : Prop :=
  t ≤ t₀ ∧ (∀ s ∈ Icc t t₀, 0 < a s) ∧ ContinuousOn a (Icc t t₀)

theorem dom_rescale {c : ℝ} (hc : 0 < c) (a : ℝ → ℝ) (t₀ t : ℝ) :
    Dom (fun s => c * a s) t₀ t ↔ Dom a t₀ t := by
  unfold Dom
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun s hs => ?_, ?_⟩
    · have := h2 s hs; by_contra h; nlinarith [not_lt.mp h]
    · refine (continuousOn_const.mul h3 : ContinuousOn (fun s => c⁻¹ * (c * a s)) _).congr ?_
      intro s _; simp only [Pi.mul_apply]; field_simp
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun s hs => mul_pos hc (h2 s hs), continuousOn_const.mul h3⟩

theorem dom_translate (τ : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) :
    Dom (fun s => a (s + τ)) (t₀ - τ) (t - τ) ↔ Dom a t₀ t := by
  unfold Dom
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, fun s hs => ?_, ?_⟩
    · have := h2 (s - τ) ⟨by linarith [hs.1], by linarith [hs.2]⟩
      simpa using this
    · have hm : MapsTo (fun s : ℝ => s - τ) (Icc t t₀) (Icc (t - τ) (t₀ - τ)) :=
        fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
      refine (h3.comp (continuousOn_id.sub continuousOn_const) hm).congr ?_
      intro s _; simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, fun s hs => h2 (s + τ) ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    have hm : MapsTo (fun s : ℝ => s + τ) (Icc (t - τ) (t₀ - τ)) (Icc t t₀) :=
      fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact h3.comp (continuousOn_id.add continuousOn_const) hm

open Classical in
/-- The program's angular-diameter distance, shifted by one off the admissible domain. -/
noncomputable def angOff (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  if Dom a t₀ t then angDist K a t₀ t else angDist K a t₀ t + 1

open Classical in
/-- The program's luminosity distance, shifted by one off the admissible domain. -/
noncomputable def lumOff (K : ℝ) (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ :=
  if Dom a t₀ t then lumDist K a t₀ t else lumDist K a t₀ t + 1

theorem angOff_spec : AngDistSpec angOff where
  flat a t₀ t htt hpos hc := by
    rw [angOff, ite_eq_left ⟨htt, hpos, hc⟩]; exact angDist_meets_spec.flat a t₀ t htt hpos hc
  closed a t₀ t htt hpos hc := by
    rw [angOff, ite_eq_left ⟨htt, hpos, hc⟩]; exact angDist_meets_spec.closed a t₀ t htt hpos hc
  «open» a t₀ t htt hpos hc := by
    rw [angOff, ite_eq_left ⟨htt, hpos, hc⟩]; exact angDist_meets_spec.open a t₀ t htt hpos hc
  rescale c hc K a t₀ t := by
    unfold angOff
    by_cases h : Dom a t₀ t
    · rw [ite_eq_left ((dom_rescale hc a t₀ t).2 h), ite_eq_left h, angDist_meets_spec.rescale c hc K a t₀ t]
    · rw [ite_eq_right (fun h' => h ((dom_rescale hc a t₀ t).1 h')), ite_eq_right h,
        angDist_meets_spec.rescale c hc K a t₀ t]
  translate τ K a t₀ t := by
    unfold angOff
    by_cases h : Dom a t₀ t
    · rw [ite_eq_left ((dom_translate τ a t₀ t).2 h), ite_eq_left h, angDist_meets_spec.translate τ K a t₀ t]
    · rw [ite_eq_right (fun h' => h ((dom_translate τ a t₀ t).1 h')), ite_eq_right h,
        angDist_meets_spec.translate τ K a t₀ t]
  deSitter t ht := by
    rw [angOff, ite_eq_left ⟨ht, fun s _ => Real.exp_pos s, Real.continuous_exp.continuousOn⟩]
    exact angDist_meets_spec.deSitter t ht
  deSitterContracting t ht := by
    rw [angOff, ite_eq_left ⟨ht, fun s _ => Real.exp_pos _, (by fun_prop : Continuous fun s : ℝ => Real.exp (-s)).continuousOn⟩]
    exact angDist_meets_spec.deSitterContracting t ht
  milne t h0 h1 := by
    rw [angOff, ite_eq_left ⟨h1, fun s hs => lt_of_lt_of_le h0 hs.1, continuousOn_id⟩]
    exact angDist_meets_spec.milne t h0 h1
  staticClosed R hR t₀ t htt := by
    rw [angOff, ite_eq_left ⟨htt, fun _ _ => hR, continuousOn_const⟩]
    exact angDist_meets_spec.staticClosed R hR t₀ t htt
  staticFlat R hR t₀ t htt := by
    rw [angOff, ite_eq_left ⟨htt, fun _ _ => hR, continuousOn_const⟩]
    exact angDist_meets_spec.staticFlat R hR t₀ t htt

theorem lumOff_spec : LumDistSpec lumOff where
  deSitter t ht := by
    rw [lumOff, ite_eq_left ⟨ht, fun s _ => Real.exp_pos s, Real.continuous_exp.continuousOn⟩]
    exact lumDist_meets_spec.deSitter t ht
  milne t h0 h1 := by
    rw [lumOff, ite_eq_left ⟨h1, fun s hs => lt_of_lt_of_le h0 hs.1, continuousOn_id⟩]
    exact lumDist_meets_spec.milne t h0 h1
  staticClosed t₀ t htt := by
    rw [lumOff, ite_eq_left ⟨htt, fun _ _ => one_pos, continuousOn_const⟩]
    exact lumDist_meets_spec.staticClosed t₀ t htt
  rescale c hc K a t₀ t := by
    unfold lumOff
    by_cases h : Dom a t₀ t
    · rw [ite_eq_left ((dom_rescale hc a t₀ t).2 h), ite_eq_left h, lumDist_meets_spec.rescale c hc K a t₀ t]
    · rw [ite_eq_right (fun h' => h ((dom_rescale hc a t₀ t).1 h')), ite_eq_right h,
        lumDist_meets_spec.rescale c hc K a t₀ t]

theorem lumOff_spec2 : LumDistSpec2 lumOff where
  base := lumOff_spec
  etherington := ⟨angOff, angOff_spec, fun K a t₀ t htt hpos hc => by
    rw [lumOff, angOff, ite_eq_left ⟨htt, hpos, hc⟩, ite_eq_left ⟨htt, hpos, hc⟩]
    obtain ⟨DA, hDA, hE⟩ := lumDist_meets_spec2.etherington
    rw [hE K a t₀ t htt hpos hc, angDistSpec_pins DA hDA K a t₀ t htt hpos hc]⟩

/-- A scale factor with a jump at the origin: positive, not continuous on [−1, 1]. -/
noncomputable def jump (s : ℝ) : ℝ := if s ≤ 0 then 1 else 2

theorem jump_pos : ∀ s ∈ Icc (-1 : ℝ) 1, 0 < jump s := fun s _ => by
  unfold jump; split_ifs <;> norm_num

theorem jump_not_cont : ¬ ContinuousOn jump (Icc (-1 : ℝ) 1) := by
  intro h
  have hivt := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) h
  have hm : (3 / 2 : ℝ) ∈ Icc (jump (-1)) (jump 1) := by
    simp only [jump]; norm_num
  obtain ⟨s, -, hs⟩ := hivt hm
  unfold jump at hs; split_ifs at hs <;> norm_num at hs



theorem lumOff_off {K : ℝ} {a : ℝ → ℝ} {t₀ t : ℝ} (h : ¬ Dom a t₀ t) : lumOff K a t₀ t = lumDist K a t₀ t + 1 := by
  rw [lumOff, ite_eq_right h]

theorem angOff_off {K : ℝ} {a : ℝ → ℝ} {t₀ t : ℝ} (h : ¬ Dom a t₀ t) : angOff K a t₀ t = angDist K a t₀ t + 1 := by
  rw [angOff, ite_eq_right h]

theorem comoving_off {a : ℝ → ℝ} {t₀ t : ℝ} (h : ¬ Dom a t₀ t) (hA : a t₀ * (1 + redshift a t₀ t) ≠ 0) :
    ¬ comoving a t₀ t = lumOff 0 a t₀ t / (a t₀ * (1 + redshift a t₀ t)) := by
  intro heq
  have hL : lumDist 0 a t₀ t = a t₀ * (1 + redshift a t₀ t) * comoving a t₀ t := by
    simp [lumDist, transverse]
  rw [lumOff_off h, hL, eq_div_iff hA] at heq
  linarith

/-! The three bad points: emission after observation; a negative scale factor; a scale factor with a jump. -/

theorem late_hpos : ∀ s ∈ Icc (1 : ℝ) 0, 0 < (fun _ : ℝ => (1 : ℝ)) s := fun _ _ => one_pos
theorem late_not : ¬ Dom (fun _ => (1 : ℝ)) 0 1 := fun h => by linarith [h.1]
theorem late_A : (fun _ : ℝ => (1 : ℝ)) 0 * (1 + redshift (fun _ => (1 : ℝ)) 0 1) ≠ 0 := by
  simp [redshift]
theorem neg_not : ¬ Dom (fun _ => (-1 : ℝ)) 0 0 := fun h => by
  have := h.2.1 0 ⟨le_rfl, le_rfl⟩; norm_num at this
theorem neg_A : (fun _ : ℝ => (-1 : ℝ)) 0 * (1 + redshift (fun _ => (-1 : ℝ)) 0 0) ≠ 0 := by
  simp [redshift]
theorem jump_not : ¬ Dom jump 1 (-1) := fun h => jump_not_cont h.2.2
theorem jump_A : jump 1 * (1 + redshift jump 1 (-1)) ≠ 0 := by
  simp [redshift, jump]; norm_num

/-- Emission before observation is needed in `lumDistSpec2_pins`. -/
theorem lumDistSpec2_pins_h2 : necessity% Checked.Fidelity.lumDistSpec2_pins 2 := by
  refine ⟨lumOff, lumOff_spec2, 0, fun _ => 1, 0, 1, late_hpos, continuousOn_const, ?_⟩
  rw [lumOff_off late_not]; simp

/-- Positivity of the scale factor is needed in `lumDistSpec2_pins`. -/
theorem lumDistSpec2_pins_h3 : necessity% Checked.Fidelity.lumDistSpec2_pins 3 := by
  refine ⟨lumOff, lumOff_spec2, 0, fun _ => -1, 0, 0, le_rfl, continuousOn_const, ?_⟩
  rw [lumOff_off neg_not]; simp

/-- Continuity of the scale factor is needed in `lumDistSpec2_pins`. -/
theorem lumDistSpec2_pins_h4 : necessity% Checked.Fidelity.lumDistSpec2_pins 4 := by
  refine ⟨lumOff, lumOff_spec2, 0, jump, 1, -1, by norm_num, jump_pos, ?_⟩
  rw [lumOff_off jump_not]; simp

/-- Emission before observation is needed in `angDistSpec_pins`. -/
theorem angDistSpec_pins_h2 : necessity% Checked.Fidelity.angDistSpec_pins 2 := by
  refine ⟨angOff, angOff_spec, 0, fun _ => 1, 0, 1, late_hpos, continuousOn_const, ?_⟩
  rw [angOff_off late_not]; simp

/-- Positivity of the scale factor is needed in `angDistSpec_pins`. -/
theorem angDistSpec_pins_h3 : necessity% Checked.Fidelity.angDistSpec_pins 3 := by
  refine ⟨angOff, angOff_spec, 0, fun _ => -1, 0, 0, le_rfl, continuousOn_const, ?_⟩
  rw [angOff_off neg_not]; simp

/-- Continuity of the scale factor is needed in `angDistSpec_pins`. -/
theorem angDistSpec_pins_h4 : necessity% Checked.Fidelity.angDistSpec_pins 4 := by
  refine ⟨angOff, angOff_spec, 0, jump, 1, -1, by norm_num, jump_pos, ?_⟩
  rw [angOff_off jump_not]; simp

/-- Emission before observation is needed in `lumDistFlat_pins`. -/
theorem lumDistFlat_pins_h2 : necessity% Checked.Fidelity.lumDistFlat_pins 2 := by
  refine ⟨lumOff, lumOff_spec2, fun _ => 1, 0, 1, late_hpos, continuousOn_const, ?_⟩
  rw [lumOff_off late_not, lumDistFlat_eq_lumDist]; simp

/-- Positivity of the scale factor is needed in `lumDistFlat_pins`. -/
theorem lumDistFlat_pins_h3 : necessity% Checked.Fidelity.lumDistFlat_pins 3 := by
  refine ⟨lumOff, lumOff_spec2, fun _ => -1, 0, 0, le_rfl, continuousOn_const, ?_⟩
  rw [lumOff_off neg_not, lumDistFlat_eq_lumDist]; simp

/-- Continuity of the scale factor is needed in `lumDistFlat_pins`. -/
theorem lumDistFlat_pins_h4 : necessity% Checked.Fidelity.lumDistFlat_pins 4 := by
  refine ⟨lumOff, lumOff_spec2, jump, 1, -1, by norm_num, jump_pos, ?_⟩
  rw [lumOff_off jump_not, lumDistFlat_eq_lumDist]; simp

/-- Emission before observation is needed in `comoving_pins`. -/
theorem comoving_pins_h2 : necessity% Checked.Fidelity.comoving_pins 2 :=
  ⟨lumOff, lumOff_spec2, fun _ => 1, 0, 1, late_hpos, continuousOn_const, comoving_off late_not late_A⟩

/-- Positivity of the scale factor is needed in `comoving_pins`. -/
theorem comoving_pins_h3 : necessity% Checked.Fidelity.comoving_pins 3 :=
  ⟨lumOff, lumOff_spec2, fun _ => -1, 0, 0, le_rfl, continuousOn_const, comoving_off neg_not neg_A⟩

/-- Continuity of the scale factor is needed in `comoving_pins`. -/
theorem comoving_pins_h4 : necessity% Checked.Fidelity.comoving_pins 4 :=
  ⟨lumOff, lumOff_spec2, jump, 1, -1, by norm_num, jump_pos, comoving_off jump_not jump_A⟩

end Checked.Trust.NCV
