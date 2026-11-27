import Checked.Chemistry.Coexistence
import Checked.Sim.Duffing
import Checked.Sim.MichaelisMenten
import Checked.Sim.Robertson
import Checked.Cosmography.BambaDLy
import Checked.Trust.SecondReadingSpecE
import Checked.Trust.SecondReadingSpecF

/-!
# Blind specification readings E and F against six more pinned definitions (run 2026-11-27T0228Z)

Third batch of `Checked/Trust/SpecAgreement.lean` (same theorem names and shapes, same namespace):
`IsCriticalIsotherm`, `IsMaxwellCoexistence`, `IsDuffingSolution`, `IsMMSolution`, `IsRobSolution`,
`comoving`. Both readers wrote from memory.

Proved disagreements:
* `not_meets_IsCriticalIsotherm_E`, `_F`: both readers require the isotherm and its derivative to be
  differentiable at the critical volume; the program's condition uses Lean's `deriv`, which is zero where
  no derivative exists, so a pressure with a jump at `v` meets the program's condition. Equivalent where
  the two derivatives exist (`pins_IsCriticalIsotherm_E`, `_F`).
* `not_meets_IsMaxwellCoexistence_E`, `_F`: both readers require the isotherm to be integrable between the
  two volumes; the program's equal-area condition uses Lean's integral, which is zero for a non-integrable
  function, so `p v = v⁻¹ − v` with `ps = 0` on volumes zero to one meets the program's condition.
  Equivalent for integrable isotherms (`pins_IsMaxwellCoexistence_E`, `_F`).
* `not_meets_IsDuffingSolution_F`, `not_meets_IsMMSolution_F`, `not_meets_IsRobSolution_F`: reader F requires
  a non-negative final time; the program's solution notion holds vacuously on an empty time interval.
  Equivalent when the final time is non-negative.
-/

namespace Checked.Trust.SpecAgreement

open Set MeasureTheory Filter Topology
open Checked.Chemistry.CubicEOS Checked.Chemistry.Coexistence Checked.Sim.Duffing
open Checked.Sim.MichaelisMenten Checked.Sim.Robertson Checked.Cosmography.BambaY
open Checked.Trust.SecondReadingSpecE Checked.Trust.SecondReadingSpecF

/-! ## Critical isotherm -/

/-- A pressure with a jump at volume zero (value one there, zero elsewhere). -/
noncomputable def jumpP : ℝ → ℝ := fun x => if x = 0 then 1 else 0

lemma jumpP_not_diff : ¬ DifferentiableAt ℝ jumpP 0 := by
  intro h
  have hc := h.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
  have h0 : Tendsto jumpP (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [jumpP, Set.mem_compl_singleton_iff.1 hx]
  have := tendsto_nhds_unique hc h0
  simp [jumpP] at this

lemma deriv_jumpP : deriv jumpP = fun _ => 0 := by
  funext x
  by_cases hx : x = 0
  · subst hx; exact deriv_zero_of_not_differentiableAt jumpP_not_diff
  · have : jumpP =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [jumpP, show y ≠ 0 from hy]
    rw [this.deriv_eq]; simp

lemma jumpP_critical : IsCriticalIsotherm jumpP 0 := by
  unfold IsCriticalIsotherm
  rw [deriv_jumpP]; simp

/-- **Disagreement (proved):** the jump pressure meets the program's critical-point condition at volume
zero (both `deriv`s vanish), not reader E's (no derivative exists there). -/
theorem not_meets_IsCriticalIsotherm_E : ¬ CriticalSpecE IsCriticalIsotherm := fun h =>
  jumpP_not_diff ((h.iff_ jumpP 0).1 jumpP_critical).1

theorem not_meets_IsCriticalIsotherm_F : ¬ CriticalSpecF IsCriticalIsotherm := fun h =>
  jumpP_not_diff ((h.iff_inflection jumpP 0).1 jumpP_critical).1

theorem pins_IsCriticalIsotherm_E (P : (ℝ → ℝ) → ℝ → Prop) (h : CriticalSpecE P) (p : ℝ → ℝ) (v : ℝ)
    (h1 : DifferentiableAt ℝ p v) (h2 : DifferentiableAt ℝ (deriv p) v) :
    P p v ↔ IsCriticalIsotherm p v := by
  rw [h.iff_]; unfold IsCriticalIsotherm; tauto

theorem pins_IsCriticalIsotherm_F (P : (ℝ → ℝ) → ℝ → Prop) (h : CriticalSpecF P) (p : ℝ → ℝ) (v : ℝ)
    (h1 : DifferentiableAt ℝ p v) (h2 : DifferentiableAt ℝ (deriv p) v) :
    P p v ↔ IsCriticalIsotherm p v := by
  rw [h.iff_inflection]; unfold IsCriticalIsotherm; tauto

/-! ## Maxwell coexistence -/

/-- A non-integrable isotherm vanishing at volumes zero and one. -/
noncomputable def poleP : ℝ → ℝ := fun x => x⁻¹ - x

lemma poleP_not_int : ¬ IntervalIntegrable poleP volume 0 1 := by
  intro h
  have h' : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 := by
    have := h.add (intervalIntegral.intervalIntegrable_id (a := 0) (b := 1))
    convert this using 1
    funext x; simp [poleP]
  rw [intervalIntegrable_inv_iff] at h'
  rcases h' with h' | h'
  · norm_num at h'
  · exact h' (by simp)

lemma poleP_coexist : IsMaxwellCoexistence poleP 0 1 0 := by
  refine ⟨zero_lt_one, by simp [poleP], by simp [poleP], ?_⟩
  rw [intervalIntegral.integral_undef poleP_not_int]; ring

theorem not_meets_IsMaxwellCoexistence_E : ¬ CoexistenceSpecE IsMaxwellCoexistence := fun h =>
  poleP_not_int ((h.iff_ poleP 0 1 0).1 poleP_coexist).2.2.2.1

theorem not_meets_IsMaxwellCoexistence_F : ¬ CoexistenceSpecF IsMaxwellCoexistence := fun h =>
  poleP_not_int ((h.iff_equal_area poleP 0 1 0).1 poleP_coexist).2.2.2.1

lemma equal_area_iff {p : ℝ → ℝ} {vl vg ps : ℝ} (hi : IntervalIntegrable p volume vl vg) :
    (∫ v in vl..vg, (p v - ps)) = 0 ↔ (∫ v in vl..vg, p v) = ps * (vg - vl) := by
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul]
  constructor <;> intro e <;> linarith

theorem pins_IsMaxwellCoexistence_E (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) (h : CoexistenceSpecE P)
    (p : ℝ → ℝ) (vl vg ps : ℝ) (hi : IntervalIntegrable p volume vl vg) :
    P p vl vg ps ↔ IsMaxwellCoexistence p vl vg ps := by
  rw [h.iff_]; unfold IsMaxwellCoexistence; rw [equal_area_iff hi]; tauto

theorem pins_IsMaxwellCoexistence_F (P : (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop) (h : CoexistenceSpecF P)
    (p : ℝ → ℝ) (vl vg ps : ℝ) (hi : IntervalIntegrable p volume vl vg) :
    P p vl vg ps ↔ IsMaxwellCoexistence p vl vg ps := by
  rw [h.iff_equal_area]; unfold IsMaxwellCoexistence; rw [equal_area_iff hi]; tauto

/-! ## Duffing oscillator -/

lemma duffing_iff_E (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) :
    IsDuffingSolution k β x₀ v₀ T x ↔
      ∃ w : ℝ → ℝ, (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt x (w t) (Icc 0 T) t) ∧
        (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt w (-(k * x t + β * (x t) ^ 3)) (Icc 0 T) t) ∧
        x 0 = x₀ ∧ w 0 = v₀ := by
  constructor
  · rintro ⟨h0, v, hv0, hv⟩
    exact ⟨v, fun t ht => (hv t ht).1, fun t ht => (hv t ht).2.congr_deriv (by ring), h0, hv0⟩
  · rintro ⟨w, h1, h2, h0, hw0⟩
    exact ⟨h0, w, hw0, fun t ht => ⟨h1 t ht, (h2 t ht).congr_deriv (by ring)⟩⟩

theorem meets_IsDuffingSolution_E : DuffingSpecE IsDuffingSolution := ⟨duffing_iff_E⟩

theorem pins_IsDuffingSolution_E (P : ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) (h : DuffingSpecE P)
    (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) : P k β x₀ v₀ T x ↔ IsDuffingSolution k β x₀ v₀ T x := by
  rw [h.iff_, duffing_iff_E]

lemma duffing_empty : IsDuffingSolution 0 0 0 0 (-1) (fun _ => 0) :=
  ⟨rfl, fun _ => 0, rfl, fun t ht => absurd (ht.1.trans ht.2) (by norm_num)⟩

theorem not_meets_IsDuffingSolution_F : ¬ DuffingSpecF IsDuffingSolution := fun h => by
  have := ((h.iff_ode 0 0 0 0 (-1) (fun _ => 0)).1 duffing_empty).1
  norm_num at this

theorem pins_IsDuffingSolution_F (P : ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) (h : DuffingSpecF P)
    (k β x₀ v₀ T : ℝ) (x : ℝ → ℝ) (hT : 0 ≤ T) :
    P k β x₀ v₀ T x ↔ IsDuffingSolution k β x₀ v₀ T x := by
  rw [h.iff_ode]
  constructor
  · rintro ⟨_, x', x'', h1, h2, h0, hv0, he⟩
    exact ⟨h0, x', hv0, fun t ht => ⟨h1 t ht, (h2 t ht).congr_deriv (by rw [he t ht]; ring)⟩⟩
  · rintro ⟨h0, v, hv0, hv⟩
    exact ⟨hT, v, fun t => -k * x t - β * x t ^ 3, fun t ht => (hv t ht).1, fun t ht => (hv t ht).2,
      h0, hv0, fun t _ => by ring⟩

/-! ## Michaelis–Menten mechanism -/

lemma mm_iff_E (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) :
    IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔
    ((∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt s (-k₁ * s t * e t + km₁ * c t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt e (-k₁ * s t * e t + (km₁ + k₂) * c t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt c (k₁ * s t * e t - (km₁ + k₂) * c t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt p (k₂ * c t) (Icc 0 T) t) ∧
     s 0 = s₀ ∧ e 0 = e₀ ∧ c 0 = c₀ ∧ p 0 = p₀) := by
  constructor
  · rintro ⟨hs, he, hc, hp, hd⟩
    exact ⟨fun t ht => (hd t ht).1.congr_deriv (by ring), fun t ht => (hd t ht).2.1.congr_deriv (by ring),
      fun t ht => (hd t ht).2.2.1.congr_deriv (by ring), fun t ht => (hd t ht).2.2.2, hs, he, hc, hp⟩
  · rintro ⟨d1, d2, d3, d4, hs, he, hc, hp⟩
    exact ⟨hs, he, hc, hp, fun t ht => ⟨(d1 t ht).congr_deriv (by ring), (d2 t ht).congr_deriv (by ring),
      (d3 t ht).congr_deriv (by ring), d4 t ht⟩⟩

theorem meets_IsMMSolution_E : MMSpecE IsMMSolution := ⟨mm_iff_E⟩

theorem pins_IsMMSolution_E
    (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) (h : MMSpecE P)
    (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) :
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔ IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p := by
  rw [h.iff_, mm_iff_E]

lemma mm_empty : IsMMSolution 0 0 0 0 0 0 0 (-1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨rfl, rfl, rfl, rfl, fun t ht => absurd (ht.1.trans ht.2) (by norm_num)⟩

theorem not_meets_IsMMSolution_F : ¬ MMSpecF IsMMSolution := fun h => by
  have := ((h.iff_ode 0 0 0 0 0 0 0 (-1) _ _ _ _).1 mm_empty).1
  norm_num at this

theorem pins_IsMMSolution_F
    (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) (h : MMSpecF P)
    (k₁ km₁ k₂ s₀ e₀ c₀ p₀ T : ℝ) (s e c p : ℝ → ℝ) (hT : 0 ≤ T) :
    P k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p ↔ IsMMSolution k₁ km₁ k₂ s₀ e₀ c₀ p₀ T s e c p := by
  rw [h.iff_ode]
  constructor
  · rintro ⟨_, d1, d2, d3, d4, hs, he, hc, hp⟩
    exact ⟨hs, he, hc, hp, fun t ht => ⟨d1 t ht, d2 t ht, d3 t ht, d4 t ht⟩⟩
  · rintro ⟨hs, he, hc, hp, hd⟩
    exact ⟨hT, fun t ht => (hd t ht).1, fun t ht => (hd t ht).2.1, fun t ht => (hd t ht).2.2.1,
      fun t ht => (hd t ht).2.2.2, hs, he, hc, hp⟩

/-! ## Robertson network -/

lemma rob_iff_E (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ) :
    IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔
    ((∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * (y₂ t) ^ 2) (Icc 0 T) t) ∧
     (∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt y₃ (k₃ * (y₂ t) ^ 2) (Icc 0 T) t) ∧
     y₁ 0 = a₀ ∧ y₂ 0 = b₀ ∧ y₃ 0 = c₀) := by
  constructor
  · rintro ⟨h1, h2, h3, hd⟩
    exact ⟨fun t ht => (hd t ht).1, fun t ht => (hd t ht).2.1, fun t ht => (hd t ht).2.2, h1, h2, h3⟩
  · rintro ⟨d1, d2, d3, h1, h2, h3⟩
    exact ⟨h1, h2, h3, fun t ht => ⟨d1 t ht, d2 t ht, d3 t ht⟩⟩

theorem meets_IsRobSolution_E : RobSpecE IsRobSolution := ⟨rob_iff_E⟩

theorem pins_IsRobSolution_E
    (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) (h : RobSpecE P)
    (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ) :
    P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔ IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ := by
  rw [h.iff_, rob_iff_E]

lemma rob_empty : IsRobSolution 0 0 0 0 0 0 (-1) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨rfl, rfl, rfl, fun t ht => absurd (ht.1.trans ht.2) (by norm_num)⟩

theorem not_meets_IsRobSolution_F : ¬ RobSpecF IsRobSolution := fun h => by
  have := ((h.iff_ode 0 0 0 0 0 0 (-1) _ _ _).1 rob_empty).1
  norm_num at this

theorem pins_IsRobSolution_F
    (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) (h : RobSpecF P)
    (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ) (hT : 0 ≤ T) :
    P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔ IsRobSolution k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ := by
  rw [h.iff_ode]
  constructor
  · rintro ⟨_, d1, d2, d3, h1, h2, h3⟩
    exact ⟨h1, h2, h3, fun t ht => ⟨d1 t ht, d2 t ht, d3 t ht⟩⟩
  · rintro ⟨h1, h2, h3, hd⟩
    exact ⟨hT, fun t ht => (hd t ht).1, fun t ht => (hd t ht).2.1, fun t ht => (hd t ht).2.2, h1, h2, h3⟩

/-! ## Comoving distance -/

theorem meets_comoving_E : ComovingSpecE comoving := ⟨fun _ _ _ _ _ _ => rfl⟩

theorem pins_comoving_E (X : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : ComovingSpecE X) (a : ℝ → ℝ) (t₀ t : ℝ)
    (htt : t ≤ t₀) (hc : ContinuousOn a (Icc t t₀)) (hpos : ∀ s ∈ Icc t t₀, 0 < a s) :
    X a t₀ t = comoving a t₀ t :=
  h.formula a t₀ t htt hc hpos

theorem meets_comoving_F : ComovingSpecF comoving :=
  ⟨fun _ _ _ _ _ => by unfold comoving; simp only [one_div]⟩

theorem pins_comoving_F (X : (ℝ → ℝ) → ℝ → ℝ → ℝ) (h : ComovingSpecF X) (a : ℝ → ℝ) (t₀ t : ℝ)
    (hc : ContinuousOn a (uIcc t t₀)) (hpos : ∀ s ∈ uIcc t t₀, 0 < a s) :
    X a t₀ t = comoving a t₀ t := by
  rw [h.eq_integral a t₀ t hc hpos, meets_comoving_F.eq_integral a t₀ t hc hpos]

end Checked.Trust.SpecAgreement
