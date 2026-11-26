import Mathlib

/-!
Blind restatement: H₂⁺, clamped nuclei, R = 2 bohr, atomic units.
Total energy E = ε + 1/R = ε + 1/2, where ε is the electronic eigenvalue.
Separated equations (ψ = L(ξ) M(η), m = 0, R = 2, ε = E - 1/2):
  ((ξ²-1) L')' + (4ξ + 2εξ² - A) L = 0     on ξ > 1
  ((1-η²) M')' + (A - 2εη²) M = 0          on -1 < η < 1
-/

open Set Filter

/-- Radial (ξ) equation, expanded: (ξ²-1) L'' + 2ξ L' + (4ξ + 2εξ² - A) L = 0. -/
def RadialEq (ε A : ℝ) (L L' L'' : ℝ → ℝ) : Prop :=
  ∀ ξ ∈ Ioi (1 : ℝ),
    HasDerivAt L (L' ξ) ξ ∧ HasDerivAt L' (L'' ξ) ξ ∧
    (ξ ^ 2 - 1) * L'' ξ + 2 * ξ * L' ξ + (4 * ξ + 2 * ε * ξ ^ 2 - A) * L ξ = 0

/-- Angular (η) equation, expanded: (1-η²) M'' - 2η M' + (A - 2εη²) M = 0. -/
def AngularEq (ε A : ℝ) (M M' M'' : ℝ → ℝ) : Prop :=
  ∀ η ∈ Ioo (-1 : ℝ) 1,
    HasDerivAt M (M' η) η ∧ HasDerivAt M' (M'' η) η ∧
    (1 - η ^ 2) * M'' η - 2 * η * M' η + (A - 2 * ε * η ^ 2) * M η = 0

theorem blind_h2plus :
    ∃ (E A : ℝ) (L L' L'' M M' M'' : ℝ → ℝ),
      E ∈ Icc (-0.6026342144950 : ℝ) (-0.6026342144949) ∧
      -- separated ODEs with electronic energy ε = E - 1/R = E - 1/2
      RadialEq (E - 1 / 2) A L L' L'' ∧
      AngularEq (E - 1 / 2) A M M' M'' ∧
      -- regularity at ξ = 1 and η = ±1 (the singular endpoints): continuous up to the boundary
      ContinuousOn L (Ici 1) ∧
      ContinuousOn M (Icc (-1) 1) ∧
      -- bound state: L decays and ψ is square integrable in ξ (weight ξ², from ξ²-η² ≤ ξ²)
      Tendsto L atTop (nhds 0) ∧
      IntegrableOn (fun ξ => L ξ ^ 2 * ξ ^ 2) (Ici 1) ∧
      -- ground state: no nodal surface, so both factors are strictly positive
      (∀ ξ ∈ Ici (1 : ℝ), 0 < L ξ) ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, 0 < M η) := by
  sorry
