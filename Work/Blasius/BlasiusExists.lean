import Mathlib
import Work.Blasius.BExFlow
import Work.Blasius.BExBounds

/-!
# Fluid mechanics: existence of a Blasius boundary layer (frozen before proof, run 2026-11-07T1228Z)

Companion of `Work/Blasius/Blasius.lean`: there is a solution f of f''' + f f''/2 = 0 on [0, ∞)
(f has derivative p, p has derivative q, q has derivative −f q/2, one-sided at 0) with
f(0) = p(0) = 0 and p(η) → 1 (classical: Töpfer 1912, Weyl 1942). Together with the wall-shear
theorem it shows that the bound there is not vacuous.

Only Mathlib definitions occur in the statement.
-/

namespace Work.Blasius
open Set Filter Topology

/-- Blasius boundary layer, existence: there are functions f, p, q on the reals such that f has
derivative p, p has derivative q and q has derivative −f q/2 on [0, ∞) (one-sided at 0), with
f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞. -/
theorem blasius_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η / 2)) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) := by
  obtain ⟨Y, hY0, hY⟩ := BExFlow.exists_flow
  obtain ⟨S, α, hα, hlim⟩ := BExBounds.inactive Y hY0 hY
  set c : ℝ := Real.sqrt α with hcdef
  have hc : 0 < c := Real.sqrt_pos.2 hα
  have hc2 : c ^ 2 = α := Real.sq_sqrt hα.le
  have S' := BTail.scale S hc
  refine ⟨fun t => (Y (t / c)).1 / c, fun t => (Y (t / c)).2.1 / c ^ 2,
    fun t => (Y (t / c)).2.2 / c ^ 3, S'.hf, S'.hp, S'.hq, ?_, ?_, ?_⟩
  · simp [hY0]
  · simp [hY0]
  · have h := (hlim.comp (tendsto_id.atTop_div_const hc)).div_const (c ^ 2)
    have e : α / c ^ 2 = 1 := by rw [hc2, div_self hα.ne']
    rw [e] at h
    exact h

end Work.Blasius
