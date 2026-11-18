import Checked.Math.BonnorEbertCountMain

/-! Bonnor–Ebert sphere, `BonnorEbertCount`: the exact number of radii at which the pressure-confined mass takes a given positive value (the number of equilibrium isothermal spheres of given mass, temperature and external pressure), for every value: none above the critical mass, one at it, and between consecutive extreme values a count that grows by one at every extreme value; infinitely many at the limit value of the mass; the first five extreme values enclosed. Promoted from `Work/Math/BonnorEbertCount.lean` (frozen, proved and audited by run 2026-11-18T1628Z); the route is `BonnorEbertCountMain`. -/

namespace Checked.Math.BonnorEbertCount
open Set Filter Topology

/-- Bonnor–Ebert sphere, number of radii of a given mass: for every solution w of
w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ
continuous at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii
ξ(0) < ξ(1) < … tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, m(ξ(0)) between 1.1822265
and 1.1822266, m(ξ(1)) between 0.694366 and 0.694367, m(ξ(2)) between 0.8306 and 0.8308, m(ξ(3)) between
0.787992 and 0.787995 and m(ξ(4)) between 0.80091 and 0.800916, and m(ξ(k)) tending to √(2/π), such that,
with N(μ) the number of radii s ≥ 0 with m(s) = μ: no radius s ≥ 0 has m(s) = μ for μ > m(ξ(0));
N(m(ξ(0))) = 1; for every k, N(μ) = 2k + 2 for m(ξ(2k+2)) < μ < m(ξ(2k)) and N(m(ξ(2k+2))) = 2k + 3;
N(μ) = 1 for 0 < μ < m(ξ(1)); for every k, N(m(ξ(2k+1))) = 2k + 2 and N(μ) = 2k + 3 for
m(ξ(2k+1)) < μ < m(ξ(2k+3)); and N(√(2/π)) = ⊤. -/
theorem bonnor_ebert_count (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      1.1822265 ≤ ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi) ≤ 1.1822266 ∧
      0.694366 ≤ ξ 1 ^ 2 * (-φ (ξ 1)) * Real.exp (w (ξ 1) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 1 ^ 2 * (-φ (ξ 1)) * Real.exp (w (ξ 1) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.694367 ∧
      0.8306 ≤ ξ 2 ^ 2 * (-φ (ξ 2)) * Real.exp (w (ξ 2) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 2 ^ 2 * (-φ (ξ 2)) * Real.exp (w (ξ 2) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.8308 ∧
      0.787992 ≤ ξ 3 ^ 2 * (-φ (ξ 3)) * Real.exp (w (ξ 3) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 3 ^ 2 * (-φ (ξ 3)) * Real.exp (w (ξ 3) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.787995 ∧
      0.80091 ≤ ξ 4 ^ 2 * (-φ (ξ 4)) * Real.exp (w (ξ 4) / 2) / Real.sqrt (4 * Real.pi) ∧
      ξ 4 ^ 2 * (-φ (ξ 4)) * Real.exp (w (ξ 4) / 2) / Real.sqrt (4 * Real.pi) ≤ 0.800916 ∧
      Tendsto (fun k => ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi))
        atTop (𝓝 (Real.sqrt (2 / Real.pi))) ∧
      (∀ μ : ℝ,
        ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi) < μ →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ} = ∅) ∧
      {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)}.encard = 1 ∧
      (∀ k : ℕ, ∀ μ : ℝ,
        ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi) < μ →
        μ < ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) /
            Real.sqrt (4 * Real.pi) →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ,
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)}.encard = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ μ : ℝ, 0 < μ →
        μ < ξ 1 ^ 2 * (-φ (ξ 1)) * Real.exp (w (ξ 1) / 2) / Real.sqrt (4 * Real.pi) →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = 1) ∧
      (∀ k : ℕ,
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi)}.encard = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, ∀ μ : ℝ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < μ →
        μ < ξ (2 * k + 3) ^ 2 * (-φ (ξ (2 * k + 3))) * Real.exp (w (ξ (2 * k + 3)) / 2) /
            Real.sqrt (4 * Real.pi) →
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) =
          Real.sqrt (2 / Real.pi)}.encard = ⊤ :=
  Checked.Math.BonnorEbertCountMain.main w φ hw hφ0 hφ h0

end Checked.Math.BonnorEbertCount
