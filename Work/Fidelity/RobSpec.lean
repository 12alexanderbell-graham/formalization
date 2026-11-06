import Mathlib

/-!
# Blind specification for Robertson's kinetics predicate

Robertson's network (textbook mass-action kinetics):
* `A → B`          rate `k₁ [A]`
* `B + C → A + C`  rate `k₂ [B][C]`   (C is a catalyst: net change 0)
* `2B → B + C`     rate `k₃ [B]²`     (net: one B consumed, one C produced)

Rate equations, with `y₁ = [A]`, `y₂ = [B]`, `y₃ = [C]`:
* `y₁' = -k₁ y₁ + k₂ y₂ y₃`
* `y₂' =  k₁ y₁ - k₂ y₂ y₃ - k₃ y₂²`
* `y₃' =  k₃ y₂²`
-/

set_option linter.dupNamespace false

namespace Work.Fidelity.RobSpec

open Set Real

/-- Reference definition: initial values at `t = 0` and the Robertson rate system on `[0, T]`,
derivatives taken within `Icc 0 T`. -/
def refRob (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ) : Prop :=
  y₁ 0 = a₀ ∧ y₂ 0 = b₀ ∧ y₃ 0 = c₀ ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Icc 0 T) t ∧
    HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * y₂ t ^ 2) (Icc 0 T) t ∧
    HasDerivWithinAt y₃ (k₃ * y₂ t ^ 2) (Icc 0 T) t

/-- Specification of a Robertson-solution predicate. -/
structure RobSpec
    (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop) : Prop where
  /-- Determining law: exactly the mass-action system with initial values. -/
  law : ∀ (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ),
    P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔
      (y₁ 0 = a₀ ∧ y₂ 0 = b₀ ∧ y₃ 0 = c₀ ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt y₁ (-k₁ * y₁ t + k₂ * y₂ t * y₃ t) (Icc 0 T) t ∧
          HasDerivWithinAt y₂ (k₁ * y₁ t - k₂ * y₂ t * y₃ t - k₃ * y₂ t ^ 2) (Icc 0 T) t ∧
          HasDerivWithinAt y₃ (k₃ * y₂ t ^ 2) (Icc 0 T) t)
  /-- Mass conservation: total concentration is constant on `[0, T]`. -/
  mass : ∀ (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ),
    P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ →
      ∀ t ∈ Icc (0 : ℝ) T, y₁ t + y₂ t + y₃ t = a₀ + b₀ + c₀
  /-- Closed-form anchor: with `k₂ = k₃ = 0` only `A → B` is active. -/
  anchor : ∀ (k₁ a₀ b₀ c₀ T : ℝ),
    P k₁ 0 0 a₀ b₀ c₀ T (fun t => a₀ * exp (-k₁ * t))
      (fun t => b₀ + a₀ * (1 - exp (-k₁ * t))) (fun _ => c₀)
  /-- Near miss 1 (wrong stoichiometry `y₃' = 2 k₃ y₂²`): with `k₁ = k₂ = 0`, `k₃ = 1`,
  `[A]₀ = 0, [B]₀ = 1, [C]₀ = 0`, `T = 1`, the functions `y₂ = 1/(1+t)`, `y₃ = 2 - 2/(1+t)`
  solve the wrong system but must be rejected. -/
  nearMiss_C : ¬ P 0 0 1 0 1 0 1 (fun _ => 0) (fun t => (1 + t)⁻¹) (fun t => 2 - 2 * (1 + t)⁻¹)
  /-- Near miss 2 (wrong stoichiometry `y₂' = … - 2 k₃ y₂²`): same data, the functions
  `y₂ = 1/(1+2t)`, `y₃ = (1 - 1/(1+2t))/2` solve the wrong system but must be rejected. -/
  nearMiss_B : ¬ P 0 0 1 0 1 0 1 (fun _ => 0) (fun t => (1 + 2 * t)⁻¹)
    (fun t => (1 - (1 + 2 * t)⁻¹) / 2)

/-! ### Proofs for `refRob` -/

theorem refRob_mass (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ)
    (h : refRob k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃) :
    ∀ t ∈ Icc (0 : ℝ) T, y₁ t + y₂ t + y₃ t = a₀ + b₀ + c₀ := by
  obtain ⟨h1, h2, h3, hd⟩ := h
  have hsum : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => y₁ s + y₂ s + y₃ s) 0 (Icc 0 T) t := by
    intro t ht
    obtain ⟨d1, d2, d3⟩ := hd t ht
    have := (d1.add d2).add d3
    convert this using 1
    ring
  have hc : ContinuousOn (fun s => y₁ s + y₂ s + y₃ s) (Icc 0 T) :=
    fun t ht => (hsum t ht).continuousWithinAt
  have key := constant_of_has_deriv_right_zero hc (fun x hx =>
    (hsum x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx))
  intro t ht
  rw [key t ht, h1, h2, h3]

theorem refRob_anchor (k₁ a₀ b₀ c₀ T : ℝ) :
    refRob k₁ 0 0 a₀ b₀ c₀ T (fun t => a₀ * exp (-k₁ * t))
      (fun t => b₀ + a₀ * (1 - exp (-k₁ * t))) (fun _ => c₀) := by
  refine ⟨by simp, by simp, rfl, fun t _ => ⟨?_, ?_, ?_⟩⟩
  · have he : HasDerivAt (fun t => exp (-k₁ * t)) (exp (-k₁ * t) * (-k₁)) t := by
      have := ((hasDerivAt_id t).const_mul (-k₁)).exp
      simpa using this
    have := (he.const_mul a₀).hasDerivWithinAt (s := Icc 0 T)
    convert this using 1
    ring
  · have he : HasDerivAt (fun t => exp (-k₁ * t)) (exp (-k₁ * t) * (-k₁)) t := by
      have := ((hasDerivAt_id t).const_mul (-k₁)).exp
      simpa using this
    have := ((((hasDerivAt_const t (1 : ℝ)).sub he).const_mul a₀).const_add b₀).hasDerivWithinAt
      (s := Icc 0 T)
    convert this using 1
    ring
  · convert (hasDerivAt_const t c₀).hasDerivWithinAt (s := Icc 0 T) using 1
    ring

/-- Uniqueness of derivatives within `Icc 0 1` at `0`. -/
theorem deriv_unique_Icc01 {f : ℝ → ℝ} {a b : ℝ}
    (ha : HasDerivWithinAt f a (Icc 0 1) 0) (hb : HasDerivWithinAt f b (Icc 0 1) 0) : a = b :=
  UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc zero_lt_one 0 (by simp)) ha hb

/-- `t ↦ (1 + c t)⁻¹` has derivative `-c / (1 + c t)²` where `1 + c t ≠ 0`. -/
theorem hasDerivAt_inv_lin (c t : ℝ) (ht : 1 + c * t ≠ 0) :
    HasDerivAt (fun s => (1 + c * s)⁻¹) (-c / (1 + c * t) ^ 2) t := by
  have hl : HasDerivAt (fun s => 1 + c * s) c t := by
    simpa using ((hasDerivAt_id t).const_mul c).const_add 1
  exact hl.inv ht

/-- Near miss 1 functions solve the wrong system `y₃' = 2 k₃ y₂²` (others textbook). -/
theorem nearMiss_C_solves_wrong :
    ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun _ => (0 : ℝ)) (-0 * 0 + 0 * (1 + t)⁻¹ * (2 - 2 * (1 + t)⁻¹))
        (Icc 0 1) t ∧
      HasDerivWithinAt (fun t => (1 + t)⁻¹)
        (0 * 0 - 0 * (1 + t)⁻¹ * (2 - 2 * (1 + t)⁻¹) - 1 * ((1 + t)⁻¹) ^ 2) (Icc 0 1) t ∧
      HasDerivWithinAt (fun t => 2 - 2 * (1 + t)⁻¹) (2 * 1 * ((1 + t)⁻¹) ^ 2) (Icc 0 1) t := by
  intro t ht
  have ht' : (1 : ℝ) + 1 * t ≠ 0 := by have := ht.1; positivity
  have hi := hasDerivAt_inv_lin 1 t ht'
  simp only [one_mul] at hi
  refine ⟨?_, ?_, ?_⟩
  · convert (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt (s := Icc 0 1) using 1
    ring
  · convert hi.hasDerivWithinAt (s := Icc 0 1) using 1
    field_simp
    ring
  · convert ((hi.const_mul 2).const_sub 2).hasDerivWithinAt (s := Icc 0 1) using 1
    field_simp

/-- Near miss 2 functions solve the wrong system `y₂' = … - 2 k₃ y₂²` (others textbook). -/
theorem nearMiss_B_solves_wrong :
    ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun _ => (0 : ℝ))
        (-0 * 0 + 0 * (1 + 2 * t)⁻¹ * ((1 - (1 + 2 * t)⁻¹) / 2)) (Icc 0 1) t ∧
      HasDerivWithinAt (fun t => (1 + 2 * t)⁻¹)
        (0 * 0 - 0 * (1 + 2 * t)⁻¹ * ((1 - (1 + 2 * t)⁻¹) / 2) - 2 * 1 * ((1 + 2 * t)⁻¹) ^ 2)
        (Icc 0 1) t ∧
      HasDerivWithinAt (fun t => (1 - (1 + 2 * t)⁻¹) / 2) (1 * ((1 + 2 * t)⁻¹) ^ 2)
        (Icc 0 1) t := by
  intro t ht
  have ht' : (1 : ℝ) + 2 * t ≠ 0 := by have := ht.1; positivity
  have hi := hasDerivAt_inv_lin 2 t ht'
  refine ⟨?_, ?_, ?_⟩
  · convert (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt (s := Icc 0 1) using 1
    ring
  · convert hi.hasDerivWithinAt (s := Icc 0 1) using 1
    field_simp
    ring
  · convert ((hi.const_sub 1).div_const 2).hasDerivWithinAt (s := Icc 0 1) using 1
    field_simp

theorem refRob_nearMiss_C :
    ¬ refRob 0 0 1 0 1 0 1 (fun _ => 0) (fun t => (1 + t)⁻¹) (fun t => 2 - 2 * (1 + t)⁻¹) := by
  rintro ⟨-, -, -, hd⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hgood := (hd 0 h0).2.2
  have hbad := (nearMiss_C_solves_wrong 0 h0).2.2
  have := deriv_unique_Icc01 hgood hbad
  norm_num at this

theorem refRob_nearMiss_B :
    ¬ refRob 0 0 1 0 1 0 1 (fun _ => 0) (fun t => (1 + 2 * t)⁻¹)
      (fun t => (1 - (1 + 2 * t)⁻¹) / 2) := by
  rintro ⟨-, -, -, hd⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hgood := (hd 0 h0).2.1
  have hbad := (nearMiss_B_solves_wrong 0 h0).2.1
  have := deriv_unique_Icc01 hgood hbad
  norm_num at this

theorem refRob_meets : RobSpec refRob where
  law := fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl
  mass := refRob_mass
  anchor := refRob_anchor
  nearMiss_C := refRob_nearMiss_C
  nearMiss_B := refRob_nearMiss_B

theorem spec_pins {P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ) → Prop}
    (h : RobSpec P) :
    ∀ (k₁ k₂ k₃ a₀ b₀ c₀ T : ℝ) (y₁ y₂ y₃ : ℝ → ℝ),
      P k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ ↔ refRob k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ :=
  fun k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃ => h.law k₁ k₂ k₃ a₀ b₀ c₀ T y₁ y₂ y₃

end Work.Fidelity.RobSpec
