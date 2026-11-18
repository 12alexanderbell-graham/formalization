import Mathlib
import Work.Math.GelfandPDECountValues
import Work.Math.GelfandPDECountValuesBlind

/-! Gelfand problem, exact counts of radial solutions with numerical band ends: the blind restatement
`Work.Math.GelfandPDECountValuesBlind.blind_gelfand_pde_count_values` (radial as `‖x‖ = ‖y‖ → u x = u y` for
points of the closed ball, solutions counted as restrictions to the closed ball with `Set.encard`) closed from the
frozen headline `Work.Math.GelfandPDECountValues.gelfand_pde_radial_count_values`. Written by run 2026-11-18T1028Z
(adapted from `Work.Math.GelfandPDECountBlindClosed`). -/

namespace Work.Math.GelfandPDECountValuesBlindClosed
open Set Metric InnerProductSpace Laplacian Work.Math.GelfandPDECountValuesBlind

/-- The program's solution class, as one predicate (local abbreviation for this proof only). -/
def Sol (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (ball 0 1) ∧
    ContinuousOn u (closedBall 0 1) ∧
    (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
    (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
    (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)

theorem sol_iff (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Sol lam u ↔ IsRadialClassicalSolution lam u := by
  constructor
  · rintro ⟨h1, h2, h3, ⟨g, hg⟩, h5⟩
    refine ⟨h1, h2, h3, fun x hx y hy hxy => ?_, h5⟩
    rw [hg x hx, hg y hy, hxy]
  · rintro ⟨h1, h2, h3, h4, h5⟩
    set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1 with he
    have hne : ‖e‖ = 1 := by simp [he]
    refine ⟨h1, h2, h3, ⟨fun r => u (r • e), fun x hx => ?_⟩, h5⟩
    have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.1 hx
    have hn : ‖‖x‖ • e‖ = ‖x‖ := by rw [norm_smul, hne, mul_one, Real.norm_eq_abs, abs_norm]
    exact h4 x hx (‖x‖ • e) (mem_closedBall_zero_iff.2 (by rw [hn]; exact hx')) hn.symm

/-- The restriction to the closed ball. -/
def res (u : EuclideanSpace ℝ (Fin 3) → ℝ) : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ :=
  fun x => u x

theorem mem_classes {lam : ℝ} {f : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ} :
    f ∈ solutionClasses lam ↔ ∃ u, Sol lam u ∧ f = res u := by
  constructor
  · rintro ⟨u, hu, hf⟩
    exact ⟨u, (sol_iff lam u).2 hu, hf⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, (sol_iff lam u).1 hu, rfl⟩

theorem res_eq {u v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) : res v = res u :=
  funext fun x => h x x.2

theorem res_ne {u v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : u 0 ≠ v 0) : res u ≠ res v := fun he =>
  h (congrFun he ⟨0, mem_closedBall_self zero_le_one⟩)

theorem blind_closed : ∃ lamStar lam1 lam2 : ℝ,
      (3.321992118 : ℝ) ≤ lamStar ∧ lamStar ≤ 3.321992119 ∧
      (1.664155 : ℝ) ≤ lam1 ∧ lam1 ≤ 1.664157 ∧
      (2.10852 : ℝ) ≤ lam2 ∧ lam2 ≤ 2.10858 ∧
      (∀ lam : ℝ, lamStar < lam → (solutionClasses lam).encard = 0) ∧
      (solutionClasses lamStar).encard = 1 ∧
      (∀ lam : ℝ, lam2 < lam → lam < lamStar → (solutionClasses lam).encard = 2) ∧
      (∀ lam : ℝ, 0 < lam → lam < lam1 → (solutionClasses lam).encard = 1) ∧
      (solutionClasses lam1).encard = 2 ∧
      (solutionClasses lam2).encard = 3 := by
  obtain ⟨ls, l1, l2, a1, a2, a3, a4, a5, a6, hA, hB, hC, hD, hE, hF⟩ :=
    Work.Math.GelfandPDECountValues.gelfand_pde_radial_count_values
  have one : ∀ lam (u : EuclideanSpace ℝ (Fin 3) → ℝ), Sol lam u →
      (∀ v, Sol lam v → ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, v x = u x) →
      (solutionClasses lam).encard = 1 := by
    intro lam u hu huniq
    rw [Set.encard_eq_one]
    refine ⟨res u, Set.ext fun f => ?_⟩
    rw [mem_classes, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact res_eq (huniq v hv)
    · rintro rfl; exact ⟨u, hu, rfl⟩
  have two : ∀ lam (u v : EuclideanSpace ℝ (Fin 3) → ℝ), u 0 ≠ v 0 → Sol lam u → Sol lam v →
      (∀ f, Sol lam f → (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = u x) ∨
        (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = v x)) →
      (solutionClasses lam).encard = 2 := by
    intro lam u v hne hu hv hall
    rw [Set.encard_eq_two]
    refine ⟨res u, res v, res_ne hne, Set.ext fun f => ?_⟩
    rw [mem_classes, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hall w hw with h | h
      · exact Or.inl (res_eq h)
      · exact Or.inr (res_eq h)
    · rintro (rfl | rfl)
      · exact ⟨u, hu, rfl⟩
      · exact ⟨v, hv, rfl⟩
  refine ⟨ls, l1, l2, a1, a2, a3, a4, a5, a6, fun lam hl => ?_, ?_, fun lam h1 h2 => ?_,
    fun lam h1 h2 => ?_, ?_, ?_⟩
  · rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
    intro f hf
    obtain ⟨u, hu, -⟩ := mem_classes.1 hf
    exact hA lam hl u hu
  · obtain ⟨u, hu, huniq⟩ := hB
    exact one ls u hu huniq
  · obtain ⟨u, v, hne, hu, hv, hall⟩ := hC lam h1 h2
    exact two lam u v hne hu hv hall
  · obtain ⟨u, hu, huniq⟩ := hD lam h1 h2
    exact one lam u hu huniq
  · obtain ⟨u, v, hne, hu, hv, hall⟩ := hE
    exact two l1 u v hne hu hv hall
  · obtain ⟨u, v, w, h1, h2, h3, hu, hv, hw, hall⟩ := hF
    rw [Set.encard_eq_three]
    refine ⟨res u, res v, res w, res_ne h1, res_ne h2, res_ne h3, Set.ext fun f => ?_⟩
    rw [mem_classes, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rcases hall g hg with h | h | h
      · exact Or.inl (res_eq h)
      · exact Or.inr (Or.inl (res_eq h))
      · exact Or.inr (Or.inr (res_eq h))
    · rintro (rfl | rfl | rfl)
      · exact ⟨u, hu, rfl⟩
      · exact ⟨v, hv, rfl⟩
      · exact ⟨w, hw, rfl⟩

/-- The blind statement itself, by its own type. -/
theorem blind_statement_closed :
    type_of% Work.Math.GelfandPDECountValuesBlind.blind_gelfand_pde_count_values :=
  blind_closed

end Work.Math.GelfandPDECountValuesBlindClosed
