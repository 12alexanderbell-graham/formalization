import Checked.Math.GelfandExtremaMain
import Checked.Math.BEFocus
import Checked.Math.GelfandRatioCore

/-! Gelfand problem in the three-dimensional ball, `GelfandTurningRatio`: the turning sequence of the radial solution branch of `Checked.Math.GelfandExtrema.gelfand_extrema`, with the rate at which the branch parameter approaches the value of the singular solution along it: the quotient of consecutive deviations from that value tends to minus the exponential of minus pi over the square root of seven. Planned route: in the focus coordinates x = u − 1, y = v − 2 of the homology system u' = u(3 − u − v)/s, v' = v(u − 1)/s (λ = uv; the turning points are the zeros of y, where λ − 2 = 2x), the weighted norm `Checked.Math.BEOCell.Nw` is the norm of the real Jordan basis; along a solution in the small ball of `Checked.Math.BEFocus` its logarithm has derivative (−1 + O(√Nw))/s and the polar angle in that basis (an arccosine, continuous where Nw is positive) has derivative (√7/2 + O(√Nw))/s; between consecutive zeros of y the angle advances by pi, so the logarithm of the radius advances by 2π/√7 + O(√Nw) and Nw drops by the factor exp(−2π/√7 + O(√Nw)); at a zero of y Nw is eight times x squared and the signs alternate. -/

namespace Work.Math.GelfandTurningRatio
open Set Filter Topology

/-- Gelfand problem, turning points of the radial branch: for every
solution w of w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative
φ and φ continuous at 0, with λ(s) = s² e^{w(s)}, there is a strictly increasing sequence of radii
ζ(0) < ζ(1) < … tending to infinity, with ζ(0) between 4.071496844 and 4.071496845 and λ(ζ(0)) between
3.321992118 and 3.321992119, such that λ(s) < λ(ζ(0)) for s ≥ 0 with s ≠ ζ(0); for every k,
λ(ζ(2k+1)) < λ(s) for s ≥ ζ(2k) with s ≠ ζ(2k+1), and λ(s) < λ(ζ(2k+2)) for s ≥ ζ(2k+1) with
s ≠ ζ(2k+2); for every k, λ(ζ(2k+1)) < 2 < λ(ζ(2k)); λ(s) tends to 2 as s tends to infinity; λ is
strictly increasing on [0, ζ(0)], strictly decreasing on [ζ(2k), ζ(2k+1)] and strictly increasing on
[ζ(2k+1), ζ(2k+2)] for every k; and (λ(ζ(k+1)) − 2)/(λ(ζ(k)) − 2) tends to −exp(−π/√7) as k tends to
infinity. -/
theorem gelfand_turning_ratio (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      4.071496844 ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      3.321992118 ≤ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ∧ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ≤ 3.321992119 ∧
      (∀ s ∈ Ici (0 : ℝ), s ≠ ζ 0 → s ^ 2 * Real.exp (w s) < ζ 0 ^ 2 * Real.exp (w (ζ 0))) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k)), s ≠ ζ (2 * k + 1) →
        ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < s ^ 2 * Real.exp (w s)) ∧
      (∀ k : ℕ, ∀ s ∈ Ici (ζ (2 * k + 1)), s ≠ ζ (2 * k + 2) →
        s ^ 2 * Real.exp (w s) < ζ (2 * k + 2) ^ 2 * Real.exp (w (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, ζ (2 * k + 1) ^ 2 * Real.exp (w (ζ (2 * k + 1))) < 2 ∧
        2 < ζ (2 * k) ^ 2 * Real.exp (w (ζ (2 * k)))) ∧
      Tendsto (fun s => s ^ 2 * Real.exp (w s)) atTop (𝓝 2) ∧
      StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ,
        StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      Tendsto (fun k : ℕ => (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) /
        (ζ k ^ 2 * Real.exp (w (ζ k)) - 2)) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) := by
  exact Checked.Math.GelfandRatioCore.ratio_main w φ hw hφ0 hφ h0

end Work.Math.GelfandTurningRatio
