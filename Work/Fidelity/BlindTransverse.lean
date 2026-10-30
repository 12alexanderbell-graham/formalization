import Mathlib

/-!
# Blind specification of the FLRW transverse-distance factor `S_K(χ)`

Written blind (without reading the project's definition of `transverse`).

Conventions: `c = 1`, `S K χ` is the comoving transverse distance with curvature
constant `K`:
`S_K(χ) = sin(√K χ)/√K` (K > 0), `χ` (K = 0), `sinh(√(-K) χ)/√(-K)` (K < 0),
defined for all real `K` and all real `χ`.

The field `ode` is the determining law: for each `K`, `χ ↦ S K χ` is the unique
solution of `S'' = -K S`, `S(0) = 0`, `S'(0) = 1`. The other fields are anchors.
-/

namespace Checked.Fidelity.BlindTransverse

open Real

/-- Textbook laws for the FLRW transverse-distance factor `S K χ`.
`ode` is determining by itself; the remaining fields are closed-form anchors. -/
structure TransverseSpec (S : ℝ → ℝ → ℝ) : Prop where
  /-- Determining law: `S K` is twice differentiable on all of `ℝ` and solves
  `S'' = -K S` with `S(0) = 0`, `S'(0) = 1`. -/
  ode : ∀ K : ℝ, ∃ S' : ℝ → ℝ,
    (∀ χ, HasDerivAt (S K) (S' χ) χ) ∧
    (∀ χ, HasDerivAt S' (-K * S K χ) χ) ∧
    S K 0 = 0 ∧ S' 0 = 1
  /-- Flat case. -/
  flat : ∀ χ, S 0 χ = χ
  /-- Closed spherical case. -/
  closed : ∀ K, 0 < K → ∀ χ, S K χ = Real.sin (Real.sqrt K * χ) / Real.sqrt K
  /-- Open hyperbolic case. -/
  open_ : ∀ K, K < 0 → ∀ χ, S K χ = Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)
  /-- Unit sphere anchor. -/
  unit_closed : ∀ χ, S 1 χ = Real.sin χ
  /-- Unit hyperboloid anchor. -/
  unit_open : ∀ χ, S (-1) χ = Real.sinh χ
  /-- Oddness in `χ`. -/
  odd : ∀ K χ, S K (-χ) = -S K χ

/-! ## Sanity checks -/

/-- Reference three-case formula. -/
noncomputable def refS (K χ : ℝ) : ℝ :=
  if 0 < K then Real.sin (Real.sqrt K * χ) / Real.sqrt K
  else if K = 0 then χ
  else Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K)

lemma refS_pos {K : ℝ} (hK : 0 < K) :
    refS K = fun χ => Real.sin (Real.sqrt K * χ) / Real.sqrt K := by
  funext χ; simp [refS, hK]

lemma refS_zero : refS 0 = fun χ => χ := by
  funext χ; simp [refS]

lemma refS_neg {K : ℝ} (hK : K < 0) :
    refS K = fun χ => Real.sinh (Real.sqrt (-K) * χ) / Real.sqrt (-K) := by
  funext χ; simp [refS, (not_lt.2 hK.le), hK.ne]

theorem refS_spec : TransverseSpec refS where
  ode K := by
    rcases lt_trichotomy K 0 with hK | rfl | hK
    · -- K < 0
      have hs : 0 < Real.sqrt (-K) := Real.sqrt_pos.2 (by linarith)
      have hss : Real.sqrt (-K) * Real.sqrt (-K) = -K := Real.mul_self_sqrt (by linarith)
      refine ⟨fun χ => Real.cosh (Real.sqrt (-K) * χ), ?_, ?_, ?_, ?_⟩
      · intro χ
        rw [refS_neg hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt (-K))).sinh.div_const (Real.sqrt (-K))
        convert h using 1
        field_simp
      · intro χ
        rw [refS_neg hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt (-K))).cosh
        convert h using 1
        field_simp
        linear_combination (-Real.sinh (Real.sqrt (-K) * χ)) * hss
      · simp [refS_neg hK]
      · simp
    · -- K = 0
      refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩
      · intro χ; rw [refS_zero]; exact hasDerivAt_id χ
      · intro χ; simpa using hasDerivAt_const χ (1 : ℝ)
      · simp [refS_zero]
      · rfl
    · -- K > 0
      have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
      have hss : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK.le
      refine ⟨fun χ => Real.cos (Real.sqrt K * χ), ?_, ?_, ?_, ?_⟩
      · intro χ
        rw [refS_pos hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt K)).sin.div_const (Real.sqrt K)
        convert h using 1
        field_simp
      · intro χ
        rw [refS_pos hK]
        have h := ((hasDerivAt_id' χ).const_mul (Real.sqrt K)).cos
        convert h using 1
        field_simp
        linear_combination (Real.sin (Real.sqrt K * χ)) * hss
      · simp [refS_pos hK]
      · simp
  flat χ := by simp [refS]
  closed K hK χ := by simp [refS, hK]
  open_ K hK χ := by simp [refS, (not_lt.2 hK.le), hK.ne]
  unit_closed χ := by simp [refS]
  unit_open χ := by
    have : ¬ (0 : ℝ) < -1 := by norm_num
    simp [refS, this]
  odd K χ := by
    unfold refS
    split_ifs <;> simp [mul_neg, Real.sin_neg, Real.sinh_neg, neg_div]

/-- Near-miss 1: forgetting the `1/√K` normalisation is rejected (fails the flat case). -/
theorem reject_no_norm :
    ¬ TransverseSpec (fun K χ => Real.sin (Real.sqrt K * χ)) := by
  intro h
  have := h.flat 1
  simp at this

/-- Near-miss 2: the sign-flipped curvature (`S'' = +K S`) is rejected. -/
theorem reject_sign_flip :
    ¬ TransverseSpec (fun K χ => refS (-K) χ) := by
  intro h
  have h1 := h.unit_closed 1
  have h2 := refS_spec.unit_open 1
  change refS (-1) 1 = Real.sin 1 at h1
  rw [h2] at h1
  have a : Real.sin 1 < 1 := Real.sin_lt one_pos
  have b : (1 : ℝ) < Real.sinh 1 := Real.self_lt_sinh_iff.2 one_pos
  linarith

/-- Near-miss 3: the `ode` field *alone* rejects the un-normalised candidate
(at `K = 0` it is identically `0`, so `S'(0) = 0 ≠ 1`). -/
theorem reject_no_norm_by_ode :
    ¬ (∀ K : ℝ, ∃ S' : ℝ → ℝ,
        (∀ χ, HasDerivAt (fun χ => Real.sin (Real.sqrt K * χ)) (S' χ) χ) ∧
        (∀ χ, HasDerivAt S' (-K * Real.sin (Real.sqrt K * χ)) χ) ∧
        Real.sin (Real.sqrt K * 0) = 0 ∧ S' 0 = 1) := by
  intro h
  obtain ⟨S', hd, -, -, h1⟩ := h 0
  have hd0 := hd 0
  simp only [Real.sqrt_zero, zero_mul, Real.sin_zero] at hd0
  have := hd0.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  rw [h1] at this
  exact one_ne_zero this

end Checked.Fidelity.BlindTransverse
