import Mathlib
import Closure.TargetRFrozen

/-! # Target R: hypotheses of the frozen headlines, needed or redundant (run 2026-11-27T0628Z).
NEEDED = dropping the hypothesis gives a statement Lean refutes; REDUNDANT = Lean proves the
statement with and without it equivalent. -/

open Complex

namespace TargetR.Necessity

theorem zeta_neg_two : riemannZeta (-2) = 0 := by
  have := riemannZeta_neg_two_mul_nat_add_one 0; simpa using this

theorem L_one_neg_two : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) (-2) = 0 := by
  rw [DirichletCharacter.LFunction_modOne_eq]; exact zeta_neg_two

/-- RH, hypothesis "not a trivial zero": NEEDED (s = -2). -/
theorem RZ_triv_needed :
    ¬ ∀ s : ℂ, riemannZeta s = 0 → s ≠ 1 → s.re = 1 / 2 := by
  intro h; have := h (-2) zeta_neg_two (by norm_num); norm_num at this

/-- RH, hypothesis `s ≠ 1`: REDUNDANT (Mathlib's `riemannZeta 1 ≠ 0`). -/
theorem RZ_one_redundant : Frozen.RiemannZetaZerosOnLine ↔
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s.re = 1 / 2 := by
  refine ⟨fun h s hz ht => h s hz ht ?_, fun h s hz ht _ => h s hz ht⟩
  rintro rfl; exact riemannZeta_ne_zero_of_one_le_re (by simp) hz

/-- Half-plane form, hypothesis `1/2 < re s`: NEEDED (N = 1, s = -2). -/
theorem NV_half_needed : ¬ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h; exact h 1 1 (-2) (Or.inr (by norm_num)) L_one_neg_two

/-- Strip forms, hypothesis `0 < re s`: NEEDED (N = 1, the primitive character, s = -2). -/
theorem ZL_pos_needed : ¬ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 := by
  intro h; have := h 1 1 (-2) (by norm_num) L_one_neg_two; norm_num at this

theorem PZ_pos_needed : ¬ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 := by
  intro h
  have := h 1 1 DirichletCharacter.isPrimitive_one_level_one (-2) (by norm_num) L_one_neg_two
  norm_num at this

/-- Primitive strip form, hypothesis `re s < 1`: REDUNDANT. -/
theorem PZ_lt_one_redundant : Frozen.PrimitiveDirichletLZerosOnLine ↔ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → ∀ s : ℂ, 0 < s.re → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 := by
  refine ⟨fun h N _ χ hχ s h0 hz => ?_, fun h N _ χ hχ s h0 _ hz => h N χ hχ s h0 hz⟩
  by_cases h1 : s.re < 1
  · exact h N χ hχ s h0 h1 hz
  exfalso
  push Not at h1
  by_cases hχ1 : χ = 1
  · subst hχ1
    have hN : N = 1 := by
      have := hχ; unfold DirichletCharacter.IsPrimitive at this
      rw [DirichletCharacter.conductor_one] at this; exact this.symm
    subst hN
    rw [DirichletCharacter.LFunction_modOne_eq] at hz
    exact riemannZeta_ne_zero_of_one_le_re h1 hz
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h1 hz

/-- The two hypotheses left open are both the junk value at the pole: for the half-plane form
`(χ ≠ 1 ∨ s ≠ 1)`, and for the all-character strip form `re s < 1`, each is redundant iff
Mathlib's value of the principal L-function at its pole is nonzero for every modulus. -/
theorem ZL_lt_one_iff_junk :
    (∀ (N : ℕ) [NeZero N], DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) 1 ≠ 0) →
    (Frozen.DirichletLZerosOnLine ↔ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2) := by
  intro hj
  refine ⟨fun h N _ χ s h0 hz => ?_, fun h N _ χ s h0 _ hz => h N χ s h0 hz⟩
  by_cases h1 : s.re < 1
  · exact h N χ s h0 h1 hz
  exfalso; push Not at h1
  by_cases hc : χ ≠ 1 ∨ s ≠ 1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hc h1 hz
  · push Not at hc; obtain ⟨rfl, rfl⟩ := hc; exact hj N hz

end TargetR.Necessity
#print axioms TargetR.Necessity.zeta_neg_two
#print axioms TargetR.Necessity.L_one_neg_two
#print axioms TargetR.Necessity.RZ_triv_needed
#print axioms TargetR.Necessity.RZ_one_redundant
#print axioms TargetR.Necessity.NV_half_needed
#print axioms TargetR.Necessity.ZL_pos_needed
#print axioms TargetR.Necessity.PZ_pos_needed
#print axioms TargetR.Necessity.PZ_lt_one_redundant
#print axioms TargetR.Necessity.ZL_lt_one_iff_junk
