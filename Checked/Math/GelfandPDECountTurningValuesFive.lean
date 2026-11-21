import Checked.Math.GelfandPDECountTurningMain
import Checked.Math.GelfandTurningValuesFive

/-! Gelfand problem in the three-dimensional ball as a PDE, `GelfandPDECountTurningValuesFive`: the number of radial classical solutions for every positive parameter, as in `Checked.Math.GelfandPDECountTurning`, with the value of the branch parameter at its fourth and fifth turning points enclosed as well. Promoted from `Work/Math/GelfandPDECountTurningValuesFive.lean` (frozen, proved and audited by run 2026-11-21T1028Z); the route is `Checked.Math.GelfandPDECountTurningMain.cset_encard` and `Checked.Math.BonnorEbertCountMain.count_abstract` applied to the turning sequence of `Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five`. -/

namespace Checked.Math.GelfandPDECountTurningValuesFive
open Set Filter Topology InnerProductSpace Laplacian Metric

/-- Gelfand problem in the unit ball of three-dimensional space, number of radial solutions. A radial solution
for the parameter lam is a function u that is twice continuously differentiable on the open unit ball, continuous on
the closed unit ball, zero on the unit sphere and a function of ‖x‖ on the closed ball, with Δu + lam e^u = 0 on
the open ball (Δ is Mathlib's Laplacian); N(lam) is the number of functions g on the closed ball such that
g x = u x on the closed ball for a radial solution u for lam. There is a sequence `lamT` of parameters, with
`lamT 0` between 3.321992118 and 3.321992119, `lamT 1` between 1.664155 and 1.664157 and `lamT 2` between 2.10852
and 2.10858, `lamT 3` between 1.967422 and 1.967510, `lamT 4` between 2.009926 and 2.010028, `lamT (2 * k)` strictly decreasing in k, `lamT (2 * k + 1)`
strictly increasing in k,
`lamT (2 * k + 1)` < 2 < `lamT (2 * k)` for every k, and `lamT` tending to 2, such that: N(lam) = 0 for
lam > `lamT 0`; N(`lamT 0`) = 1; for every k, N(lam) = 2k + 2 for `lamT (2 * k + 2)` < lam < `lamT (2 * k)` and
N(`lamT (2 * k + 2)`) = 2k + 3; N(lam) = 1 for 0 < lam < `lamT 1`; for every k, N(`lamT (2 * k + 1)`) = 2k + 2
and N(lam) = 2k + 3 for `lamT (2 * k + 1)` < lam < `lamT (2 * k + 3)`; and N(2) = ⊤. -/
theorem gelfand_pde_radial_count_turning_values_five :
    ∃ lamT : ℕ → ℝ,
      3.321992118 ≤ lamT 0 ∧ lamT 0 ≤ 3.321992119 ∧
      1.664155 ≤ lamT 1 ∧ lamT 1 ≤ 1.664157 ∧ 2.10852 ≤ lamT 2 ∧ lamT 2 ≤ 2.10858 ∧
      1.967422 ≤ lamT 3 ∧ lamT 3 ≤ 1.967510 ∧ 2.009926 ≤ lamT 4 ∧ lamT 4 ≤ 2.010028 ∧
      StrictAnti (fun k : ℕ => lamT (2 * k)) ∧ StrictMono (fun k : ℕ => lamT (2 * k + 1)) ∧
      (∀ k : ℕ, lamT (2 * k + 1) < 2 ∧ 2 < lamT (2 * k)) ∧
      Tendsto lamT atTop (𝓝 2) ∧
      (∀ lam : ℝ, lamT 0 < lam →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 0) ∧
      {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT 0 * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 1 ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 2) < lam → lam < lamT (2 * k) →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ,
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT (2 * k + 2) * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ lam : ℝ, 0 < lam → lam < lamT 1 →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = 1) ∧
      (∀ k : ℕ,
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lamT (2 * k + 1) * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, ∀ lam : ℝ, lamT (2 * k + 1) < lam → lam < lamT (2 * k + 3) →
        {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      {g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ | ∃ u : EuclideanSpace ℝ (Fin 3) → ℝ,
          (ContDiffOn ℝ 2 u (ball 0 1) ∧ ContinuousOn u (closedBall 0 1) ∧
          (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0) ∧
          (∃ h : ℝ → ℝ, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, u x = h ‖x‖) ∧
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + 2 * Real.exp (u x) = 0)) ∧
          ∀ x : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, g x = u x}.encard = ⊤ := by
  obtain ⟨W, Φ, hw, hφ0, hφ, h0⟩ := Checked.Math.BEGlobalExists.exists_global
  obtain ⟨ζ, hmono, htop, hz0lo, hz0hi, hl0lo, hl0hi, hl1lo, hl1hi, hl2lo, hl2hi, hl3lo, hl3hi, hl4lo, hl4hi,
    hmax0, hmin, hmax, hband, hlim, hinc0, hdec, hinc⟩ :=
    Checked.Math.GelfandTurningValuesFive.gelfand_turning_values_five W Φ hw hφ0 hφ h0
  set Λ : ℝ → ℝ := fun s => s ^ 2 * Real.exp (W s) with hΛ
  have cW : ContinuousOn W (Ici 0) := fun t ht => (hw t ht).continuousWithinAt
  have cΛ : ContinuousOn Λ (Ici 0) := (continuousOn_id.pow 2).mul cW.rexp
  have Λ0 : Λ 0 = 0 := by simp [hΛ]
  have hz0 : 0 < ζ 0 := by norm_num at hz0lo; linarith
  have Λpos : ∀ s, 0 < s → 0 < Λ s := fun s hs => by simp only [hΛ]; positivity
  have hzpos : ∀ k, 0 < ζ k := fun k => lt_of_lt_of_le hz0 (hmono.monotone (Nat.zero_le k))
  obtain ⟨cA, cB, cC, cD, cE, cF, cG, cH⟩ :=
    Checked.Math.BonnorEbertCountMain.count_abstract Λ ζ 2 two_pos cΛ Λ0 hmono hz0
      (Λpos _ (hzpos 1)) hmax0 hmin hmax hband hinc0 hdec hinc
  have key := fun lam (hl : 0 < lam) =>
    Checked.Math.GelfandPDECountTurningMain.cset_encard W Φ hw hφ0 hφ h0 lam hl
  have lpos : ∀ k, 0 < Λ (ζ k) := fun k => Λpos _ (hzpos k)
  refine ⟨fun k => Λ (ζ k), hl0lo, hl0hi, hl1lo, hl1hi, hl2lo, hl2hi, hl3lo, hl3hi,
    hl4lo, hl4hi, ?_, ?_, hband, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine strictAnti_nat_of_succ_lt fun k => ?_
    rcases k with _ | j
    · exact hmax0 (ζ 2) (hzpos 2).le (hmono.injective.ne (by norm_num))
    · have h := hmax j (ζ (2 * (j + 1) + 2))
        (hmono.monotone (by omega)) (hmono.injective.ne (by omega))
      simpa [show 2 * (j + 1 + 1) = 2 * (j + 1) + 2 by ring, show 2 * j + 2 = 2 * (j + 1) by ring]
        using h
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have h2 := hmin k (ζ (2 * (k + 1) + 1)) (hmono.monotone (by omega))
      (hmono.injective.ne (by omega))
    exact h2
  · exact hlim.comp htop
  · intro lam hl
    exact (key lam (by linarith [lpos 0])).trans (cA lam hl)
  · exact (key _ (lpos 0)).trans cB
  · intro k lam h1 h2
    exact (key lam (by linarith [lpos (2 * k + 2)])).trans (cC k lam h1 h2)
  · intro k
    exact (key _ (lpos _)).trans (cD k)
  · intro lam hl h1
    exact (key lam hl).trans (cE lam hl h1)
  · intro k
    exact (key _ (lpos _)).trans (cF k)
  · intro k lam h1 h2
    exact (key lam (by linarith [lpos (2 * k + 1)])).trans (cG k lam h1 h2)
  · exact (key 2 two_pos).trans cH


end Checked.Math.GelfandPDECountTurningValuesFive
