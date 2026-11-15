import Checked.Math.BEMonoMain

/-! Bonnor–Ebert sphere, `BonnorEbertMonotone`: the claim of `Checked.Math.BonnorEbertExtrema.bonnor_ebert_extrema` for the same sequence of extrema, together with the strict monotonicity of the pressure-confined mass on the segment from the centre to the first maximum and on every segment between consecutive extrema, so that the sequence contains every local extremum of the mass. Promoted from `Work/Math/BonnorEbertMono.lean` (frozen, proved and audited by run 2026-11-15T0828Z); the route is `BEMonoMain`. -/

namespace Checked.Math.BonnorEbertMonotone
open Set Filter Topology

/-- Bonnor–Ebert sphere, extrema and monotone segments of the mass: for every solution w of
w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ
continuous at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii
ξ(0) < ξ(1) < … tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, such that m(s) < m(ξ(0)) for
s ≥ 0 with s ≠ ξ(0); for every k, m(ξ(2k+1)) < m(s) for s ≥ ξ(2k) with s ≠ ξ(2k+1), and m(s) < m(ξ(2k+2))
for s ≥ ξ(2k+1) with s ≠ ξ(2k+2); for every k, m(ξ(2k+1)) < √(2/π) < m(ξ(2k)); m(s) tends to √(2/π) as s
tends to infinity; m is strictly increasing on [0, ξ(0)]; and for every k, m is strictly decreasing on
[ξ(2k), ξ(2k+1)] and strictly increasing on [ξ(2k+1), ξ(2k+2)]. -/
theorem bonnor_ebert_extrema_monotone (w φ : ℝ → ℝ)
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
        (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) :=
  Checked.Math.BEMonoMain.main w φ hw hφ0 hφ h0

end Checked.Math.BonnorEbertMonotone
