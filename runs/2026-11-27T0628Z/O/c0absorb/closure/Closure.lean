import Mathlib
import Readings.C0Absorb
import ComparatorChallenges.C0Absorption

/-! # Target O, family O34 (bi-Lipschitz absorption of c₀ without a linear copy of c₀): closures
(run 2026-11-27T0628Z). Frozen statement taken with `type_of%`, never retyped: `MainConclusion` — a separable real
Banach Z with no bounded-below linear map c₀ → Z (`NoLinearC0`, c₀ = `C₀(ℕ, ℝ)`), an onto bi-Lipschitz
F : Z × c₀ → Z (max norm), and more. Closed: reader C (c₀ = `ZeroAtInftyContinuousMap ℕ ℝ`, the frozen one; a closed
subspace Y ≃L c₀ would give the bounded-below map c₀ ≃ Y ⊆ Z). Not closed: readers A and B, who define c₀ as the
subspace of ℓ^∞ of sequences tending to 0 — isometrically isomorphic to `C₀(ℕ, ℝ)`, but the isomorphism is not
written here. -/

namespace TargetO.C0Absorb

open OAI.C0Absorption

theorem no_copy {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (h : NoLinearC0 Z) :
    ¬ (∃ Y : Submodule ℝ Z, IsClosed (Y : Set Z) ∧ Nonempty (Y ≃L[ℝ] ZeroAtInftyContinuousMap ℕ ℝ)) := by
  rintro ⟨Y, -, ⟨e⟩⟩
  set E : Y →L[ℝ] ZeroAtInftyContinuousMap ℕ ℝ := (e : Y →L[ℝ] ZeroAtInftyContinuousMap ℕ ℝ)
  have hE : 0 ≤ ‖E‖ := ContinuousLinearMap.opNorm_nonneg E
  refine h (Y.subtypeL.comp (e.symm : ZeroAtInftyContinuousMap ℕ ℝ →L[ℝ] Y)) ⟨1 / (‖E‖ + 1),
    by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ ‖E‖ * ‖e.symm x‖ := by
    calc ‖x‖ = ‖e (e.symm x)‖ := by rw [ContinuousLinearEquiv.apply_symm_apply]
      _ ≤ ‖E‖ * ‖e.symm x‖ := E.le_opNorm _
  have h2 : ‖(Y.subtypeL.comp (e.symm : ZeroAtInftyContinuousMap ℕ ℝ →L[ℝ] Y)) x‖ = ‖e.symm x‖ := rfl
  rw [h2, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have : 0 ≤ ‖e.symm x‖ := norm_nonneg _
  nlinarith [norm_nonneg x]

theorem C_thm : (type_of% @OAI.C0Absorption.main_result) → (type_of% @ReaderC.reading_c0absorb_thm11) := by
  rintro ⟨Z, i1, i2, hc, hs, hn, ⟨F, hF, c, C, hc0, hcC, hb⟩, -⟩
  exact ⟨Z, i1, i2, hc, hs, no_copy hn, F, hF, c, C, hc0, hcC, hb⟩

end TargetO.C0Absorb

#print axioms TargetO.C0Absorb.C_thm
