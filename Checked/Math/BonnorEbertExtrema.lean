import Checked.Math.BEAllMain

/-! Bonnor–Ebert sphere, `BonnorEbertExtrema`: every extremum of the pressure-confined mass at once, for the regular isothermal solution on the whole half-line: an infinite strictly increasing sequence of extrema tending to infinity, alternating maxima and minima, each the strict extreme of the mass from the previous extremum on, maxima above and minima below the singular isothermal sphere's value, to which the mass tends. Promoted from `Work/Math/BonnorEbertAll.lean` (frozen and proved by run 2026-11-15T0028Z); the route is `BEAllMain` (the certified chain of `BE3Ext`, then the analytic argument of `BEFocus` near the focus of the homology field). -/

namespace Checked.Math.BonnorEbertExtrema
open Set Filter Topology

/-- Bonnor–Ebert sphere, extrema of the mass: for every solution w of w'' + (2/s)w' + e^w = 0 on
(0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ continuous at 0, with
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii ξ(0) < ξ(1) < …
tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, such that m(s) < m(ξ(0)) for s ≥ 0 with
s ≠ ξ(0); for every k, m(ξ(2k+1)) < m(s) for s ≥ ξ(2k) with s ≠ ξ(2k+1), and m(s) < m(ξ(2k+2)) for
s ≥ ξ(2k+1) with s ≠ ξ(2k+2); for every k, m(ξ(2k+1)) < √(2/π) < m(ξ(2k)); and m(s) tends to √(2/π) as
s tends to infinity. -/
theorem bonnor_ebert_extrema (w φ : ℝ → ℝ)
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
        (𝓝 (Real.sqrt (2 / Real.pi))) :=
  Checked.Math.BEAllMain.main w φ hw hφ0 hφ h0

end Checked.Math.BonnorEbertExtrema
