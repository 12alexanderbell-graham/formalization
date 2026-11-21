import Checked.Math.GelfandExtremaMain
import Checked.Math.GLamBands
import Work.Math.GelfandLam4

/-! Gelfand problem in the three-dimensional ball, `GelfandTurningValuesFive`: the turning sequence of the radial solution branch of `Checked.Math.GelfandExtrema.gelfand_extrema`, with the value of the branch parameter enclosed at its first five turning points (the five values of the conclusion). Frozen by run 2026-11-21T0428Z before its proof; the planned route is `Checked.Math.GelfandExtremaMain.main`, `Checked.Math.GLamBands.bands` and `Work.Math.GelfandLam4.lam34_band`. -/

namespace Work.Math.GelfandTurningValuesFive
open Set Filter Topology

/-- Gelfand problem, turning values of the radial branch: for every
solution w of w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative
φ and φ continuous at 0, with λ(s) = s² e^{w(s)}, there is a strictly increasing sequence of radii
ζ(0) < ζ(1) < … tending to infinity, with ζ(0) between 4.071496844 and 4.071496845, λ(ζ(0)) between
3.321992118 and 3.321992119, λ(ζ(1)) between 1.664155 and 1.664157, λ(ζ(2)) between 2.10852 and 2.10858,
λ(ζ(3)) between 1.967422 and 1.967510 and λ(ζ(4)) between 2.009926 and 2.010028, such that λ(s) < λ(ζ(0)) for s ≥ 0 with s ≠ ζ(0); for every k,
λ(ζ(2k+1)) < λ(s) for s ≥ ζ(2k) with s ≠ ζ(2k+1), and λ(s) < λ(ζ(2k+2)) for s ≥ ζ(2k+1) with
s ≠ ζ(2k+2); for every k, λ(ζ(2k+1)) < 2 < λ(ζ(2k)); λ(s) tends to 2 as s tends to infinity; and λ is
strictly increasing on [0, ζ(0)], strictly decreasing on [ζ(2k), ζ(2k+1)] and strictly increasing on
[ζ(2k+1), ζ(2k+2)] for every k. -/
theorem gelfand_turning_values_five (w φ : ℝ → ℝ)
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
  obtain ⟨ζ, hm, ht, hz0lo, hz0hi, hl0lo, hl0hi, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono⟩ :=
    Checked.Math.GelfandExtremaMain.main w φ hw hφ0 hφ h0
  obtain ⟨b1, b2, b3, b4⟩ :=
    Checked.Math.GLamBands.bands w φ hw hφ0 hφ h0 ζ hm hz0lo hz0hi hinc0 hanti hmono
  obtain ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ :=
    Work.Math.GelfandLam4.lam34_band w φ hw hφ0 hφ h0 ζ hm hz0lo hz0hi hinc0 hanti hmono
  exact ⟨ζ, hm, ht, hz0lo, hz0hi, hl0lo, hl0hi, b1, b2, b3, b4, c1, c2, d1, d2, hmax0, hmin, hmax, h2, hlim,
    hinc0, hanti, hmono⟩

end Work.Math.GelfandTurningValuesFive
