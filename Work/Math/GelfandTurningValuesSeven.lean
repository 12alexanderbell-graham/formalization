import Mathlib

/-! Gelfand problem in the three-dimensional ball, `GelfandTurningValuesSeven`: the turning sequence of the radial solution branch of `Checked.Math.GelfandExtrema.gelfand_extrema`, with the value of the branch parameter enclosed at its first seven turning points (the seven values of the conclusion). Frozen by run 2026-11-21T1028Z before its proof; the planned route is `Checked.Math.GelfandExtremaMain.main`, `Checked.Math.GLamBands.bands` and `Work.Math.GelfandLam6.lam3456_band`. -/

namespace Work.Math.GelfandTurningValuesSeven
open Set Filter Topology

/-- Gelfand problem, turning values of the radial branch: for every
solution w of w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative
φ and φ continuous at 0, with λ(s) = s² e^{w(s)}, there is a strictly increasing sequence of radii
ζ(0) < ζ(1) < … tending to infinity, with ζ(0) between 4.071496844 and 4.071496845, λ(ζ(0)) between
3.321992118 and 3.321992119, λ(ζ(1)) between 1.664155 and 1.664157, λ(ζ(2)) between 2.10852 and 2.10858,
λ(ζ(3)) between 1.967422 and 1.967510, λ(ζ(4)) between 2.009926 and 2.010028, λ(ζ(5)) between 1.996901 and 1.997023
and λ(ζ(6)) between 2.000873 and 2.000980, such that λ(s) < λ(ζ(0)) for s ≥ 0 with s ≠ ζ(0); for every k,
λ(ζ(2k+1)) < λ(s) for s ≥ ζ(2k) with s ≠ ζ(2k+1), and λ(s) < λ(ζ(2k+2)) for s ≥ ζ(2k+1) with
s ≠ ζ(2k+2); for every k, λ(ζ(2k+1)) < 2 < λ(ζ(2k)); λ(s) tends to 2 as s tends to infinity; and λ is
strictly increasing on [0, ζ(0)], strictly decreasing on [ζ(2k), ζ(2k+1)] and strictly increasing on
[ζ(2k+1), ζ(2k+2)] for every k. -/
theorem gelfand_turning_values_seven (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) :
    ∃ ζ : ℕ → ℝ, StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      4.071496844 ≤ ζ 0 ∧ ζ 0 ≤ 4.071496845 ∧
      3.321992118 ≤ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ∧ ζ 0 ^ 2 * Real.exp (w (ζ 0)) ≤ 3.321992119 ∧
      1.664155 ≤ ζ 1 ^ 2 * Real.exp (w (ζ 1)) ∧ ζ 1 ^ 2 * Real.exp (w (ζ 1)) ≤ 1.664157 ∧
      2.10852 ≤ ζ 2 ^ 2 * Real.exp (w (ζ 2)) ∧ ζ 2 ^ 2 * Real.exp (w (ζ 2)) ≤ 2.10858 ∧
      1.967422 ≤ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ∧ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ≤ 1.967510 ∧
      2.009926 ≤ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ∧ ζ 4 ^ 2 * Real.exp (w (ζ 4)) ≤ 2.010028 ∧
      1.996901 ≤ ζ 5 ^ 2 * Real.exp (w (ζ 5)) ∧ ζ 5 ^ 2 * Real.exp (w (ζ 5)) ≤ 1.997023 ∧
      2.000873 ≤ ζ 6 ^ 2 * Real.exp (w (ζ 6)) ∧ ζ 6 ^ 2 * Real.exp (w (ζ 6)) ≤ 2.000980 ∧
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
        StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) := by
  sorry

end Work.Math.GelfandTurningValuesSeven
