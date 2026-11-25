import Checked.Math.BEMonoMain
import Checked.Math.GelfandRadiiCore

/-! Bonnor–Ebert sphere, `BonnorEbertTurningRatio`: the extrema of the pressure-confined mass of `Checked.Math.BonnorEbertMonotone.bonnor_ebert_extrema_monotone`, with the rate at which they approach the singular isothermal sphere: the quotient of consecutive extremum radii tends to the exponential of two pi over the square root of seven, and the quotient of consecutive deviations of the mass from the singular value tends to minus the exponential of minus pi over the square root of seven. Planned route: the extrema of the mass are the zeros of g = 2u − v in the homology variables (`Checked.Math.BEFocus`); the angle of `Checked.Math.GelfandRatioCore`, measured from the ray of g = 0 instead of the ray of v = 2, advances by pi between consecutive zeros of g, so the segment bounds of `Checked.Math.GelfandRatioCore.Sys.seg_bounds` hold with the same constants; at a zero of g the weighted norm is thirty-two (u − 1) squared and the mass is the singular value times u squared, so the quotient of deviations is the quotient of the u − 1 values times a factor tending to one, and the squeezes `Checked.Math.GelfandRatioCore.lim_D` and `Checked.Math.GelfandRadiiCore.lim_L` give both limits. -/

namespace Work.Math.BonnorEbertTurningRatio
open Set Filter Topology

/-- Bonnor–Ebert sphere, extrema and monotone segments of the mass: for every solution w of
w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ
continuous at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii
ξ(0) < ξ(1) < … tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, such that m(s) < m(ξ(0)) for
s ≥ 0 with s ≠ ξ(0); for every k, m(ξ(2k+1)) < m(s) for s ≥ ξ(2k) with s ≠ ξ(2k+1), and m(s) < m(ξ(2k+2))
for s ≥ ξ(2k+1) with s ≠ ξ(2k+2); for every k, m(ξ(2k+1)) < √(2/π) < m(ξ(2k)); m(s) tends to √(2/π) as s
tends to infinity; m is strictly increasing on [0, ξ(0)]; for every k, m is strictly decreasing on
[ξ(2k), ξ(2k+1)] and strictly increasing on [ξ(2k+1), ξ(2k+2)]; ξ(k+1)/ξ(k) tends to exp(2π/√7) as k
tends to infinity; and (m(ξ(k+1)) − √(2/π))/(m(ξ(k)) − √(2/π)) tends to −exp(−π/√7) as k tends to
infinity. -/
theorem bonnor_ebert_turning_ratio (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ξ 0 →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ 0 ^ 2 * (-φ (ξ 0)) * Real.exp (w (ξ 0) / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) <
          s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi) <
          ξ (2 * k + 2) ^ 2 * (-φ (ξ (2 * k + 2))) * Real.exp (w (ξ (2 * k + 2)) / 2) /
            Real.sqrt (4 * Real.pi)) ∧
      (∀ k : ℕ,
        ξ (2 * k + 1) ^ 2 * (-φ (ξ (2 * k + 1))) * Real.exp (w (ξ (2 * k + 1)) / 2) /
            Real.sqrt (4 * Real.pi) < Real.sqrt (2 / Real.pi) ∧
        Real.sqrt (2 / Real.pi) <
          ξ (2 * k) ^ 2 * (-φ (ξ (2 * k))) * Real.exp (w (ξ (2 * k)) / 2) / Real.sqrt (4 * Real.pi)) ∧
      Tendsto (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)) atTop
        (𝓝 (Real.sqrt (2 / Real.pi))) ∧
      StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (fun s => s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi))
        (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
        (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi))) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) := by
  sorry

end Work.Math.BonnorEbertTurningRatio
