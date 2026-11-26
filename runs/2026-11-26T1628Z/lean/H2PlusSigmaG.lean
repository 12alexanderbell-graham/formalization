import Mathlib
/-!
# The hydrogen molecular ion at internuclear distance two bohr (freeze, run 2026-11-26T1628Z)

Conventions (atomic units: ħ = mₑ = e = 4πε₀ = 1; energies in hartree; lengths in bohr).
Two clamped nuclei of charge 1 at distance R = 2; one electron. The electronic Hamiltonian is
−½Δ − 1/r₁ − 1/r₂ on ℝ³; the total (Born–Oppenheimer) energy is the electronic eigenvalue ε plus the
nuclear repulsion 1/R, so ε = E − 1/2 for the total energy E.

Prolate spheroidal coordinates ξ = (r₁ + r₂)/R ∈ [1, ∞), η = (r₁ − r₂)/R ∈ [−1, 1], azimuth φ. For an
axially symmetric state (m = 0) ψ = L(ξ) M(η) the equation −½Δψ − (1/r₁ + 1/r₂)ψ = εψ separates, with a
separation constant A, into
  d/dξ [(ξ² − 1) dL/dξ] + (2Rξ + (εR²/2) ξ² + A) L = 0,   ξ > 1,
  d/dη [(1 − η²) dM/dη] − ((εR²/2) η² + A) M = 0,         −1 < η < 1,
and at R = 2 (2R = 4, R²/2 = 2):
  ((ξ² − 1) L′)′ + (4ξ + 2ε ξ² + A) L = 0,   ((1 − η²) M′)′ − (2ε η² + A) M = 0.
The sign of A is the printed one (Madsen–Peek; Table VI of arXiv 1401.8009 prints A = 0.8117295846248 for the
ground state at R = 2; in this convention A → −ℓ(ℓ + 1) as R → 0).

Boundary conditions: L continuous on [1, ∞) (this excludes the solution with a logarithmic singularity at
ξ = 1) and L(ξ) → 0 as ξ → ∞ (this excludes the growing solution); M continuous on [−1, 1] (this excludes the
logarithmic solutions at η = ±1). No node: L > 0 on [1, ∞) and M > 0 on [−1, 1] (the 1sσ_g state has no nodal
surface). Printed total energies at R = 2: −0.6026342144949 hartree (arXiv physics/0607081) and
−1.20526842899 Ry (arXiv 1401.8009, Table I); reading `runs/2026-11-26T1628Z/tables/READING.md`.

What this statement does not say (fidelity record, for the audit): that ψ = L M is an eigenfunction of the
three-dimensional operator (the separation is the classical change of variables, not formalised here), that a
positive eigenfunction belongs to the lowest eigenvalue (a classical theorem for Schrödinger operators, not
formalised here), or that the separable solution is square integrable (it follows from L → 0 and the equation,
not stated).
-/

namespace Work.Quantum.H2Plus
open Set Filter Topology

/-- Hydrogen molecular ion at internuclear distance 2 bohr, nuclear charges 1, axially symmetric separated
equations: there is a total energy E in [−0.6026342144950, −0.6026342144949] (electronic energy E − 1/2), a
separation constant A and functions L, M with derivatives L′, M′ such that ((ξ² − 1) L′)′ + (4ξ + 2(E − 1/2)ξ² + A) L = 0
for ξ > 1, ((1 − η²) M′)′ − (2(E − 1/2)η² + A) M = 0 for −1 < η < 1, L continuous and positive on [1, ∞) with
L(ξ) → 0 as ξ → ∞, and M continuous and positive on [−1, 1]. -/
theorem h2plus_separated_energy_two :
    ∃ E ∈ Icc (-0.6026342144950 : ℝ) (-0.6026342144949), ∃ A : ℝ, ∃ L L' M M' : ℝ → ℝ,
      ContinuousOn L (Ici 1) ∧
      (∀ ξ ∈ Ioi (1 : ℝ), HasDerivAt L (L' ξ) ξ) ∧
      (∀ ξ ∈ Ioi (1 : ℝ), HasDerivAt (fun x => (x ^ 2 - 1) * L' x)
        (-((4 * ξ + 2 * (E - 1 / 2) * ξ ^ 2 + A) * L ξ)) ξ) ∧
      (∀ ξ ∈ Ici (1 : ℝ), 0 < L ξ) ∧
      Tendsto L atTop (𝓝 0) ∧
      ContinuousOn M (Icc (-1) 1) ∧
      (∀ η ∈ Ioo (-1 : ℝ) 1, HasDerivAt M (M' η) η) ∧
      (∀ η ∈ Ioo (-1 : ℝ) 1, HasDerivAt (fun x => (1 - x ^ 2) * M' x)
        ((2 * (E - 1 / 2) * η ^ 2 + A) * M η) η) ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, 0 < M η) := by
  sorry

end Work.Quantum.H2Plus
