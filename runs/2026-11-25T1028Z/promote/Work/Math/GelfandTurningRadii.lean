import Checked.Math.GelfandRatioCore
import Checked.Math.GelfandLam6Pos
import Checked.Math.GelfandRadiiCore

/-! Gelfand problem in the three-dimensional ball, `GelfandTurningRadii`: the turning sequence of the radial solution branch of `Checked.Math.GelfandTurningRatio.gelfand_turning_ratio`, with the rate at which consecutive turning radii grow: the quotient of consecutive turning radii tends to the exponential of two pi over the square root of seven, and from the seventh turning point on both that quotient and the quotient of consecutive deviations of the branch parameter from the value of the singular solution lie in explicit intervals. Planned route: the squeeze of `Checked.Math.GelfandRatioCore.lim_D` gives the limit of the advance of log s between consecutive turning points (its first two bounds alone); the four bounds of `Checked.Math.GelfandRatioCore.Sys.seg_bounds` hold with the error of the seventh turning point at every later one because the weighted norm decreases (`Sys.N_le_of`), that error is bounded by the value of the branch parameter at the seventh turning point (`Checked.Math.GelfandLam6.lam3456_band`), and the seventh turning radius lies beyond the start of the small ball (`Checked.Math.GelfandLam6Pos.zeta6_ge`). -/

namespace Work.Math.GelfandTurningRadii
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
infinity; ζ(k+1)/ζ(k) tends to exp(2π/√7) as k tends to infinity; and for every k ≥ 6, ζ(k+1)/ζ(k) is
between 10.3 and 11.2 and (λ(ζ(k+1)) − 2)/(λ(ζ(k)) − 2) is between −0.33 and −0.28. -/
theorem gelfand_turning_radii (w φ : ℝ → ℝ)
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
        (ζ k ^ 2 * Real.exp (w (ζ k)) - 2)) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) ∧
      Tendsto (fun k : ℕ => ζ (k + 1) / ζ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      (∀ k : ℕ, 6 ≤ k →
        10.3 ≤ ζ (k + 1) / ζ k ∧ ζ (k + 1) / ζ k ≤ 11.2 ∧
        -0.33 ≤ (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) ∧
        (ζ (k + 1) ^ 2 * Real.exp (w (ζ (k + 1))) - 2) / (ζ k ^ 2 * Real.exp (w (ζ k)) - 2) ≤ -0.28) := by
  exact Checked.Math.GelfandRadiiCore.radii_main w φ hw hφ0 hφ h0

end Work.Math.GelfandTurningRadii
