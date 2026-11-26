import Checked.Math.BEMonoMain
import Checked.Math.GelfandRadiiCore
import Checked.Math.BEDecayCore

/-! Bonnor–Ebert sphere, `BonnorEbertTurningDecay`: the extrema of the pressure-confined mass of `Checked.Math.BonnorEbertTurningBounds.bonnor_ebert_turning_bounds`, with bounds at every extremum from index five on that shrink geometrically: the distance of the quotient of consecutive extremum radii from its limit exp(2π/√7) is at most c₁ times q to the power n at index n + 5, and the distance of the quotient of consecutive deviations of the mass from the singular value from its limit −exp(−π/√7) is at most c₂ times q to the power n, for constants c₁ ≤ 23/10, c₂ ≤ 3/20 and a ratio 0 ≤ q ≤ 21/50 (in the proof: 23/10, 3/20 and 21/50 themselves). Planned route: the proof of `Checked.Math.BEBoundsCore.bounds_main` gives, at every extremum from index five on, the four segment bounds of `Checked.Math.BERatioCore.Sys.segB_bounds` with error ε at most 57/10000, the square root of the weighted norm at that extremum; the bound on the advance of log Nw gives ε at the next extremum at most exp(−0.882) < 21/50 times ε, so by induction ε at index n + 5 is at most 57/10000 (21/50)^n; the advance of log s differs from 2π/√7 by at most 31 ε and half the advance of log Nw from −π/√7 by at most 62 ε, so the two quotients are within 400 ε and 26 ε of their limits. -/

namespace Work.Math.BonnorEbertTurningDecay
open Set Filter Topology

/-- Bonnor–Ebert sphere, extrema and monotone segments of the mass: for every solution w of
w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ
continuous at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii
ξ(0) < ξ(1) < … tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, such that m(s) < m(ξ(0)) for
s ≥ 0 with s ≠ ξ(0); for every k, m(ξ(2k+1)) < m(s) for s ≥ ξ(2k) with s ≠ ξ(2k+1), and m(s) < m(ξ(2k+2))
for s ≥ ξ(2k+1) with s ≠ ξ(2k+2); for every k, m(ξ(2k+1)) < √(2/π) < m(ξ(2k)); m(s) tends to √(2/π) as s
tends to infinity; m is strictly increasing on [0, ξ(0)]; for every k, m is strictly decreasing on
[ξ(2k), ξ(2k+1)] and strictly increasing on [ξ(2k+1), ξ(2k+2)]; ξ(k+1)/ξ(k) tends to exp(2π/√7) as k
tends to infinity; (m(ξ(k+1)) − √(2/π))/(m(ξ(k)) − √(2/π)) tends to −exp(−π/√7) as k tends to
infinity; and for every k ≥ 5, ξ(k+1)/ξ(k) is between 9.2 and 12.9 and
(m(ξ(k+1)) − √(2/π))/(m(ξ(k)) − √(2/π)) is between −0.42 and −0.21; and there are constants c₁ ≤ 23/10,
c₂ ≤ 3/20 and a ratio q with 0 ≤ q ≤ 21/50 such that for every n,
|ξ(n+6)/ξ(n+5) − exp(2π/√7)| ≤ c₁ q^n and
|(m(ξ(n+6)) − √(2/π))/(m(ξ(n+5)) − √(2/π)) + exp(−π/√7)| ≤ c₂ q^n. -/
theorem bonnor_ebert_turning_decay (w φ : ℝ → ℝ)
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
            Real.sqrt (2 / Real.pi))) atTop (𝓝 (-Real.exp (-(Real.pi / Real.sqrt 7)))) ∧
      (∀ k : ℕ, 5 ≤ k →
        9.2 ≤ ξ (k + 1) / ξ k ∧ ξ (k + 1) / ξ k ≤ 12.9 ∧
        -0.42 ≤ (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) ∧
        (ξ (k + 1) ^ 2 * (-φ (ξ (k + 1))) * Real.exp (w (ξ (k + 1)) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) /
          (ξ k ^ 2 * (-φ (ξ k)) * Real.exp (w (ξ k) / 2) / Real.sqrt (4 * Real.pi) -
            Real.sqrt (2 / Real.pi)) ≤ -0.21) ∧
      (∃ c₁ c₂ q : ℝ, c₁ ≤ 23 / 10 ∧ c₂ ≤ 3 / 20 ∧ 0 ≤ q ∧ q ≤ 21 / 50 ∧
        ∀ n : ℕ,
          |ξ (n + 6) / ξ (n + 5) - Real.exp (2 * Real.pi / Real.sqrt 7)| ≤ c₁ * q ^ n ∧
          |(ξ (n + 6) ^ 2 * (-φ (ξ (n + 6))) * Real.exp (w (ξ (n + 6)) / 2) / Real.sqrt (4 * Real.pi) -
                Real.sqrt (2 / Real.pi)) /
              (ξ (n + 5) ^ 2 * (-φ (ξ (n + 5))) * Real.exp (w (ξ (n + 5)) / 2) / Real.sqrt (4 * Real.pi) -
                Real.sqrt (2 / Real.pi)) -
            -Real.exp (-(Real.pi / Real.sqrt 7))| ≤ c₂ * q ^ n) := by
  exact Checked.Math.BEDecayCore.decay_main w φ hw hφ0 hφ h0

end Work.Math.BonnorEbertTurningDecay
