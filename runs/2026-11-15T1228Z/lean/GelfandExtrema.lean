import Mathlib

/-! Gelfand problem in the three-dimensional ball, `GelfandExtrema` (FROZEN by run 2026-11-15T1228Z
before proof).

Same equation and conventions as `Checked/Math/Gelfand.lean` (headline `gelfand_ball_critical`) and
`Checked/Math/BonnorEbertExtrema.lean`: w'' + (2/s) w' + e^w = 0, w(0) = 0, φ = w', φ continuous at 0, the
solution given on the whole half-line [0, ∞) (one-sided derivatives within [0, ∞)). The radial solutions
of Δu + λ e^u = 0 in the unit ball of ℝ³ with u = 0 on the boundary are u(r) = w(s r) + log(s²/λ) with
λ = s² e^{w(s)}; the curve s ↦ λ(s) = s² e^{w(s)} is the radial solution branch, and its local extrema
are its turning points.

What this adds to `gelfand_ball_critical`: that headline gives only the first turning point (the
maximum λ* of λ over [0, S]). This statement gives every turning point at once: a strictly increasing
sequence ζ₀ < ζ₁ < … → ∞, ζ₀ in the window of `gelfand_ball_critical`, λ strictly increasing on [0, ζ₀],
strictly decreasing on every [ζ(2k), ζ(2k+1)], strictly increasing on every [ζ(2k+1), ζ(2k+2)]; each ζ(k)
the strict extreme of λ from the previous one on; maxima above 2 and minima below 2 (the value of the
singular solution w = log(2/s²)), and λ(s) → 2.

Route (planned, no new certificates): with u = s e^w / (−φ), v = −s φ (homology variables, u v = λ),
λ' = s e^w (2 − v), so the turning points are the zeros of v − 2. Volterra's function
(u − 1 − log u) + (v − 2 − 2 log(v/2)) has derivative −(u − 1)²/s, so it decreases; at a zero of v − 2 it
equals u − 1 − log u and λ = 2u, which orders the maxima and minima. Zeros of v − 2 are transversal
(v' = −φ (u − 1); u = 1 there would put the state at the equilibrium, where 4π m² = u v³ = 8,
contradicting the strict mass extrema of `bonnor_ebert_extrema`). v − 2 changes sign after every radius:
at a zero of 2e^w − φ² (a mass extremum, infinitely many by `bonnor_ebert_extrema`) its derivative has
the sign of 2 − v. The limit: at the turning points u v³ = 8u, and m → √(2/π) gives u → 1. -/

namespace Work.Math.GelfandExtrema
open Set Filter Topology

/-- Gelfand problem in the three-dimensional ball, turning points of the radial branch: for every
solution w of w'' + (2/s)w' + e^w = 0 on (0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative
φ and φ continuous at 0, with λ(s) = s² e^{w(s)}, there is a strictly increasing sequence of radii
ζ(0) < ζ(1) < … tending to infinity, with ζ(0) between 4.071496844 and 4.071496845 and λ(ζ(0)) between
3.321992118 and 3.321992119, such that λ(s) < λ(ζ(0)) for s ≥ 0 with s ≠ ζ(0); for every k,
λ(ζ(2k+1)) < λ(s) for s ≥ ζ(2k) with s ≠ ζ(2k+1), and λ(s) < λ(ζ(2k+2)) for s ≥ ζ(2k+1) with
s ≠ ζ(2k+2); for every k, λ(ζ(2k+1)) < 2 < λ(ζ(2k)); λ(s) tends to 2 as s tends to infinity; and λ is
strictly increasing on [0, ζ(0)], strictly decreasing on [ζ(2k), ζ(2k+1)] and strictly increasing on
[ζ(2k+1), ζ(2k+2)] for every k. -/
theorem gelfand_extrema (w φ : ℝ → ℝ)
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
        StrictMonoOn (fun s => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) := by
  sorry

end Work.Math.GelfandExtrema
