import Mathlib
import Work.Math.BEMonoMain

/-! Bonnor–Ebert sphere, `BonnorEbertMono` (FROZEN by run 2026-11-15T0828Z before proof).

Same equation and conventions as `Checked/Math/BonnorEbertExtrema.lean` (headline `bonnor_ebert_extrema`):
the isothermal (Emden–Chandrasekhar) equation w'' + (2/s) w' + e^w = 0 for w = −ψ, w(0) = 0, φ = w',
φ continuous at 0, the solution given on the whole half-line [0, ∞) (one-sided derivatives within
[0, ∞)); the pressure-confined dimensionless mass m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π).

What this adds to `bonnor_ebert_extrema`: that headline gives a sequence ξ₀ < ξ₁ < … → ∞ of strict
extrema (each the strict extreme of m from the previous one on), but does not exclude further local
extrema of m between two consecutive ξ's. This statement adds, for the same sequence, that m is strictly
increasing on [0, ξ₀], strictly decreasing on every [ξ(2k), ξ(2k+1)] and strictly increasing on every
[ξ(2k+1), ξ(2k+2)]. Together: m has no local extremum other than the ξ's, so the ξ's are exactly the
turning points of the mass–radius curve of pressure-confined isothermal spheres (the referee's open point
of run 2026-11-15T0028Z).

Route (planned): `Checked.Math.BE3Ext` and `Checked.Math.BEAllMain` with the monotonicity that their
proofs already establish exported: the sign of 2u − v (u v³ = 4π m²) from the certified chains
`BEHChain`, `BEOChain`, `BE3Chain` between the brackets, strict monotonicity of 2u − v inside each
bracket, the zeros identified with the extrema by strictness; the first maximum from
`bonnor_ebert_critical`; beyond radius 300000 the segments of `BEFocus.tail`. -/

namespace Work.Math.BonnorEbertMono
open Set Filter Topology

/-- Bonnor–Ebert sphere, extrema and monotone segments of the mass: for every solution w of
w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ
continuous at 0, with m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of
radii ξ(0) < ξ(1) < … tending to infinity, with ξ(0) between 6.4507514 and 6.4507515, with every property
of `bonnor_ebert_extrema`, and moreover m is strictly increasing on [0, ξ(0)], strictly decreasing on
[ξ(2k), ξ(2k+1)] and strictly increasing on [ξ(2k+1), ξ(2k+2)] for every k. -/
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
  Work.Math.BEMonoMain.main w φ hw hφ0 hφ h0

end Work.Math.BonnorEbertMono
