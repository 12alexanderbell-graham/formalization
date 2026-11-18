import Mathlib
import Checked.Math.BonnorEbertMonotone
import Checked.Math.BonnorEbertMax
import Checked.Math.BonnorEbertMin
import Checked.Math.BonnorEbertMax2
import Checked.Math.BonnorEbertMin2
import Checked.Math.BonnorEbertMax3

/-! Bonnor–Ebert sphere, `BonnorEbertCount` (FROZEN by run 2026-11-18T1628Z before proof).

Same equation and conventions as `Checked/Math/BonnorEbertMonotone.lean` (headline
`bonnor_ebert_extrema_monotone`): the isothermal (Emden–Chandrasekhar) equation w'' + (2/s) w' + e^w = 0
for w = −ψ, w(0) = 0, φ = w', φ continuous at 0, the solution given on the whole half-line [0, ∞)
(one-sided derivatives within [0, ∞)); the pressure-confined dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π). A pressure-confined isothermal sphere of given temperature and
external pressure is the solution cut at a radius s > 0, and its dimensionless mass is m(s); so the number
of equilibrium spheres of dimensionless mass μ is the number of radii s ≥ 0 with m(s) = μ.

What this adds: the exact number of such radii for every positive μ, with the band ends
m(ξ₀) … m(ξ₄) enclosed. The counts change exactly at the values m(ξₖ), so these are pinned as the band
ends; the limit clause pins that the bands exhaust every μ > 0 other than √(2/π), where the count is
infinite.

Planned route (no new certificates): the sequence of `bonnor_ebert_extrema_monotone` (strict extrema,
strict monotonicity on each segment, limit √(2/π)); its first five terms identified with the extremisers of
`bonnor_ebert_max`, `bonnor_ebert_min`, `bonnor_ebert_second_max`, `bonnor_ebert_second_min` and
`bonnor_ebert_third_max` (a strict extremum on [ξₖ₋₁, S] below S equals the strict extremum from ξₖ₋₁ on,
by strict monotonicity on the segment), which gives the five value windows; then a counting lemma: if μ lies
strictly between m at the two ends of each of the first N segments and strictly between m(0) and m(ξ₀), the
solutions in [0, ξ_N] are one per segment (intermediate value theorem and injectivity), and the tail beyond
ξ_N is read off the strict extremum properties. -/

namespace Work.Math.BonnorEbertCount
open Set Filter Topology

/-- Bonnor–Ebert sphere, exact number of radii of a given mass: for every solution w of
w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ
continuous at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii
ξ(0) < ξ(1) < … tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, m(ξ(0)) between 1.1822265
and 1.1822266, m(ξ(1)) between 0.694366 and 0.694367, m(ξ(2)) between 0.8306 and 0.8308, m(ξ(3)) between
0.787992 and 0.787995 and m(ξ(4)) between 0.80091 and 0.800916, and m(ξ(k)) tending to √(2/π), such that,
writing N(μ) for the number of radii s ≥ 0 with m(s) = μ: N(μ) = 0 for μ > m(ξ(0)); N(m(ξ(0))) = 1; for
every k, N(μ) = 2k + 2 for m(ξ(2k+2)) < μ < m(ξ(2k)) and N(m(ξ(2k+2))) = 2k + 3; N(μ) = 1 for
0 < μ < m(ξ(1)); for every k, N(m(ξ(2k+1))) = 2k + 2 and N(μ) = 2k + 3 for
m(ξ(2k+1)) < μ < m(ξ(2k+3)); and N(√(2/π)) is infinite. -/
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
        {s ∈ Ici (0 : ℝ) | s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) = μ}.encard
          = 0) ∧
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
          Real.sqrt (2 / Real.pi)}.encard = ⊤ := by
  sorry

end Work.Math.BonnorEbertCount
