import Mathlib
import Work.Math.GelfandPDEManyCentre
import Work.Math.GelfandPDEManyBlind

/-! Gelfand problem, multiplicity of radial solutions: the blind restatement
`Work.Math.GelfandPDEManyBlind.blind_gelfand_pde_many` (radial as `‖x‖ = ‖y‖ → u x = u y` on the closed ball,
distinctness on the closed ball, "infinitely many" as an infinite set of restrictions to the closed ball)
closed from the frozen headline `Work.Math.GelfandPDEManyCentre.gelfand_pde_radial_many_centre`: distinct
values at the centre give distinct restrictions. Written by run 2026-11-15T1828Z. -/

namespace Work.Math.GelfandPDEManyBlindClosed
open Set Filter Topology InnerProductSpace Laplacian Metric Work.Math.GelfandPDEManyBlind

theorem sol_of (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : ContDiffOn ℝ 2 u (ball 0 1) ∧
      ContinuousOn u (closedBall 0 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
      (∃ g : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = g ‖x‖) ∧
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) :
    IsRadialClassicalSol lam u := by
  obtain ⟨h1, h2, h3, ⟨g, hg⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun x hx y hy hxy => by rw [hg x hx, hg y hy, hxy], h5⟩

theorem distinct_of (u v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : u 0 ≠ v 0) : DistinctOnBall u v :=
  ⟨0, mem_closedBall_self zero_le_one, h⟩

theorem blind_closed :
    (SolRestr 2).Infinite ∧
      (∀ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ lam : ℝ, |lam - 2| < ε →
        ∃ F : Fin N → (EuclideanSpace ℝ (Fin 3) → ℝ),
          (∀ i, IsRadialClassicalSol lam (F i)) ∧
          ∀ i j, i ≠ j → DistinctOnBall (F i) (F j)) ∧
      (∀ lam : ℝ, 2 ≤ lam → lam < 3.321992118 →
        ∃ u v : EuclideanSpace ℝ (Fin 3) → ℝ,
          IsRadialClassicalSol lam u ∧ IsRadialClassicalSol lam v ∧ DistinctOnBall u v) := by
  obtain ⟨⟨u, hinj, hu⟩, hN, h3⟩ := Work.Math.GelfandPDEManyCentre.gelfand_pde_radial_many_centre
  refine ⟨?_, ?_, ?_⟩
  · -- the restrictions to the closed ball form an infinite set
    let r : ℕ → (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ) → ℝ) := fun i x => u i x
    have hr : Function.Injective r := by
      intro i j hij
      apply hinj
      have := congrFun hij ⟨0, mem_closedBall_self zero_le_one⟩
      simpa [r] using this
    refine Set.infinite_of_injective_forall_mem hr (fun i => ?_)
    exact ⟨u i, sol_of 2 (u i) (hu i), fun x => rfl⟩
  · intro N
    obtain ⟨ε, hε, h⟩ := hN N
    refine ⟨ε, hε, fun lam hl => ?_⟩
    obtain ⟨F, hFi, hF⟩ := h lam hl
    exact ⟨F, fun i => sol_of lam (F i) (hF i), fun i j hij => distinct_of _ _ (fun e => hij (hFi e))⟩
  · intro lam h2 hlt
    obtain ⟨u, v, hne, hu, hv⟩ := h3 lam h2 hlt
    exact ⟨u, v, sol_of lam u hu, sol_of lam v hv, distinct_of u v hne⟩

end Work.Math.GelfandPDEManyBlindClosed
