import Mathlib
import Readings.finitistic
import ComparatorChallenges.LittleFinitistic

/-! # Target O, family O58 (little finitistic dimension), Theorem 1.1: closures (run 2026-11-27T1628Z).

Frozen statement `OAI.LittleFinitistic.Main.exists_counterexample` (challenge `LittleFinitistic`, taken by name,
never retyped): a finite-dimensional complex algebra `A`, `littleFinitisticDimension A = ⊤`, and for every `m > 0`
a finitely generated `N` with `((2m − 2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N < ⊤` (Mathlib's Ext-based
projective dimension). The challenge `FinitisticAsymmetry` defines a constant of the same name, so the corollary is
closed in a separate module (`ClosureCor.lean`).

Links: Mathlib's `projectiveDimension_ge_iff`, `projectiveDimension_le_iff` and `projectiveDimension_ne_top_iff`
carry the frozen `WithBot ℕ∞` bounds to the readers' `HasProjectiveDimensionLT/LE`. The paper's
"finite-dimensional module" (reader A: `Module.Finite ℂ (RestrictScalars ℂ A N)`) follows from the frozen
"finitely generated over `A`" because `A` is finite-dimensional (`Module.Finite.trans`). "fin.dim A = ∞" for
readers A and B (no bound `n` on finitely generated modules of finite projective dimension) follows from the
modules `N_m` alone, at `m = n + 2`. Reader C (projective dimension by free resolutions, its own `pdFree`) is not
closed: Mathlib has no theorem relating resolution length to the Ext-based `HasProjectiveDimensionLT`. -/

namespace TargetO.Finitistic

open CategoryTheory OAI.LittleFinitistic

theorem finite_pd {R : Type} [Ring R] (N : ModuleCat.{0} R) (h : projectiveDimension N < ⊤) :
    ∃ n : ℕ, HasProjectiveDimensionLE N n :=
  (projectiveDimension_ne_top_iff N).1 (ne_of_lt h)

theorem not_lt_of_ge {R : Type} [Ring R] (N : ModuleCat.{0} R) (j : ℕ)
    (h : ((j : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N) : ¬ HasProjectiveDimensionLT N j :=
  (projectiveDimension_ge_iff N j).1 h

theorem not_le_of_ge {R : Type} [Ring R] (N : ModuleCat.{0} R) (j n : ℕ) (hjn : n < j)
    (h : ((j : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N) : ¬ HasProjectiveDimensionLE N n := by
  intro hle
  rw [← projectiveDimension_le_iff] at hle
  have := h.trans hle
  have : (j : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := this
  exact absurd (by exact_mod_cast this) (Nat.not_le.2 hjn)

/-- The frozen modules give unbounded finite projective dimensions on finitely generated modules. -/
theorem unbounded {R : Type} [Ring R]
    (hN : ∀ m : ℕ, 0 < m → ∃ N : ModuleCat.{0} R, Module.Finite R N ∧
      ((2 * m - 2 : ℕ) : WithBot ℕ∞) ≤ projectiveDimension N ∧ projectiveDimension N < ⊤) (n : ℕ) :
    ∃ N : ModuleCat.{0} R, Module.Finite R N ∧ (∃ k : ℕ, HasProjectiveDimensionLE N k) ∧
      ¬ HasProjectiveDimensionLE N n := by
  obtain ⟨N, hfin, hge, hlt⟩ := hN (n + 2) (by omega)
  exact ⟨N, hfin, finite_pd N hlt, not_le_of_ge N _ n (by omega) hge⟩

/-! ## Reader A -/

theorem closure_A (frozen : type_of% @Main.exists_counterexample) : type_of% @ReaderA.reading_thm_1_1 := by
  obtain ⟨A, _, _, hfd, _, hN⟩ := frozen
  refine ⟨A, inferInstance, inferInstance, hfd, fun m hm => ?_, fun n => unbounded hN n⟩
  obtain ⟨N, hfin, hge, hlt⟩ := hN m (by omega)
  refine ⟨N, ?_, fun i hi => not_lt_of_ge N i ?_, finite_pd N hlt⟩
  · letI : Module A (RestrictScalars ℂ A N) := RestrictScalars.moduleOrig ℂ A N
    have : Module.Finite A (RestrictScalars ℂ A N) := hfin
    exact Module.Finite.trans A (RestrictScalars ℂ A N)
  · have : 2 * m - 2 = i := by omega
    rw [← this]; exact hge

/-! ## Reader B -/

theorem closure_B (frozen : type_of% @Main.exists_counterexample) : type_of% @ReaderB.readingTheorem11 := by
  obtain ⟨A, _, _, hfd, _, hN⟩ := frozen
  refine ⟨A, inferInstance, inferInstance, hfd, fun m hm => ?_, fun n hle => ?_⟩
  · obtain ⟨N, hfin, hge, hlt⟩ := hN m (by omega)
    exact ⟨N, hfin, ⟨2 * m - 2, by omega, not_lt_of_ge N _ hge⟩, finite_pd N hlt⟩
  · obtain ⟨N, hfin, hpd, hnot⟩ := unbounded hN n
    exact hnot (hle N hfin hpd)

theorem reading_A_closed : type_of% @ReaderA.reading_thm_1_1 := closure_A Main.exists_counterexample
theorem reading_B_closed : type_of% @ReaderB.readingTheorem11 := closure_B Main.exists_counterexample

end TargetO.Finitistic

#print axioms TargetO.Finitistic.closure_A
#print axioms TargetO.Finitistic.closure_B
