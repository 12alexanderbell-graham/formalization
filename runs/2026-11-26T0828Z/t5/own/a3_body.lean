open Set Filter Topology InnerProductSpace Laplacian Metric
namespace RB3
namespace SecondReading
/-- P c: "c ≥ 3.321992119 (spelled as a natural number times 1e-9), or no solution has λ above c" -/
def P (c : ℝ) : Prop :=
  (c ≥ Real.sqrt ((3.321992119 : ℝ) ^ 2)) ∨
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    ¬ (c < lam)
def rn : Prop := P 3.321992119
end SecondReading

theorem cl : ∀ c : ℝ, SecondReading.P c ↔
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro c
  unfold SecondReading.P
  constructor
  · rintro (h | h)
    · intro lam u hu hc hb hpde
      have := Checked.Math.GelfandPDEBound.gelfand_pde_bound lam u hu hc hb hpde
      have h2 : (3.321992119 : ℝ) ≤ c := by
        rw [Real.sqrt_sq (by norm_num)] at h; exact h
      linarith
    · intro lam u hu hc hb hpde
      exact not_lt.mp (h lam u hu hc hb hpde)
  · intro h
    exact Or.inr fun lam u hu hc hb hpde => not_lt.mpr (h lam u hu hc hb hpde)

theorem cl.bite : ¬ ∀ c : ℝ,
  ∀ (lam : ℝ) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiffOn ℝ 2 u (ball 0 1))
    (hc : ContinuousOn u (closedBall 0 1))
    (hb : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → u x = 0)
    (hpde : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, Δ u x + lam * Real.exp (u x) = 0),
    lam ≤ c := by
  intro h
  obtain ⟨u, hu, hc, hb, -, hpde⟩ :=
    Checked.Math.GelfandPDEExists.gelfand_pde_radial_exists 3.3 (by norm_num) (by norm_num)
  have := h 3 3.3 u hu hc hb hpde
  norm_num at this
end RB3

open Claims in
run_cmd do
  let env ← getEnv
  let isRd := fun (c : Name) => (`RB3.SecondReading).isPrefixOf c
  let faults ← liftTermElabM <| paramClosureFaults env isRd `Checked.Math.GelfandPDEBound.gelfand_pde_bound `RB3.cl `RB3.SecondReading.rn
  logInfo m!"RESULT a3: {if faults.isEmpty then "ACCEPTED" else "REJECTED"} {faults.toList}"
