import Work.Math.GLamBands
import Work.Math.GLam3Chain

/-! Gelfand problem, `GelfandLam3` (run 2026-11-20T1028Z): the value of the branch parameter
λ(s) = s² e^{w(s)} of the regular isothermal solution at its fourth turning point (index three of the turning
sequence), for every sequence of turning points with the monotonicity pattern of
`Checked.Math.GelfandExtrema.gelfand_extrema`. Route: the route of `Work.Math.GLamBands.bands`, continued by the
certified homology cells of `GLam3Chain` from the end of `GLamChain` (v > 2 up to the bracket, u < 1 on the
bracket, v < 2 at its end), the zero of v − 2 in the bracket by the intermediate value theorem, identified with
the fourth given turning point by strict monotonicity of λ at two points, and λ = 2u at a zero of v − 2. -/

namespace Work.Math.GelfandLam3
open Set Checked.Math.GelfandExtremaMain Work.Math.GLamCell Work.Math.GLamBands

/-- For the regular solution w of the radial Gelfand (isothermal) equation w'' + (2/s) w' + e^w = 0 with
w(0) = 0, and any strictly increasing sequence ζ whose first term lies in [4.071496844, 4.071496845] and
along which λ(s) = s² e^{w(s)} increases on [0, ζ 0] and then alternately decreases and increases, the value
of λ at ζ 3 (the fourth turning point) lies in [1.9637, 1.9707]. -/
theorem lam3_band (w φ : ℝ → ℝ)
    (hw : ∀ s ∈ Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s)
    (h0 : w 0 = 0) (ζ : ℕ → ℝ) (hm : StrictMono ζ)
    (hz0lo : 4.071496844 ≤ ζ 0) (hz0hi : ζ 0 ≤ 4.071496845)
    (hinc0 : StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)))
    (hanti : ∀ k : ℕ,
      StrictAntiOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1))))
    (hmono : ∀ k : ℕ,
      StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) :
    1.9637 ≤ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ∧ ζ 3 ^ 2 * Real.exp (w (ζ 3)) ≤ 1.9707 := by
  sorry

end Work.Math.GelfandLam3
