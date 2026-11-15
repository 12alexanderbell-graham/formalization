import Mathlib
import Work.Math.BEAllMain

/-! Bonnor–Ebert sphere, `BonnorEbertAll` (FROZEN by run 2026-11-15T0028Z before proof).

Same equation and conventions as `Checked/Math/BonnorEbert.lean` and the five extremum headlines
(`bonnor_ebert_max`, `bonnor_ebert_min`, `bonnor_ebert_second_max`, `bonnor_ebert_second_min`,
`bonnor_ebert_third_max`): the isothermal (Emden–Chandrasekhar) equation w'' + (2/s) w' + e^w = 0 for w = −ψ
(ρ = ρ_c e^{−ψ}), w(0) = 0, φ = w', φ continuous at 0; the pressure-confined dimensionless mass
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π). The difference to the earlier headlines: the solution is given on the
whole half-line [0, ∞) (one-sided derivatives within [0, ∞)), not on a bounded interval [0, S].

The earlier headlines certify the first five extrema one turn of the spiral at a time. This file states every
extremum at once: the mass has infinitely many extrema ξ₀ < ξ₁ < ξ₂ < … → ∞ (ξ₀ the critical sphere, in the
same seven-decimal window as `bonnor_ebert_critical`); even indices are maxima, odd indices minima; each maximum
is the strict maximum of the mass over every radius from the previous minimum on (the first one over every
radius), each minimum is the strict minimum over every radius from the previous maximum on; every maximum lies
strictly above √(2/π) and every minimum strictly below it; and the mass tends to √(2/π) (the singular
isothermal sphere's value) as the radius tends to infinity. Physically: the mass–radius curve of
pressure-confined isothermal spheres oscillates forever with shrinking amplitude about its limit; no
radius beyond the first minimum ever again reaches a mass outside the band between consecutive extrema.

Route (planned): the certified chain of `BE3Main` up to radius 300000 (state there within 4·10⁻⁷ of
a rational point ≈ 0.0057 from the focus (1, 2) of the homology field in the weighted norm of `BEOCell`), then
an analytic argument with no new certificates: in the weighted ball of radius 1/20 about the focus the
weighted norm decreases (Lyapunov), the angular momentum about the focus is positive, so the ratio
(u − 1)/(2u − v) increases at a rate ≥ c/s and 2u − v must change sign again; at each zero of 2u − v its
derivative is 8u(1 − u)/s ≠ 0, the mass is u² √(2/π), and the weighted norm there is 32 (u − 1)². -/

namespace Work.Math.BonnorEbertAll
open Set Filter Topology

/-- Bonnor–Ebert sphere, every extremum of the mass: for every solution w of w'' + (2/s)w' + e^w = 0 on
(0, ∞) with w(0) = 0, w differentiable on [0, ∞) with derivative φ and φ continuous at 0, with
m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π), there is a strictly increasing sequence of radii ξ₀ < ξ₁ < … tending
to infinity, with ξ₀ between 6.4507514 and 6.4507515, such that m(s) < m(ξ₀) for every other s ≥ 0, for
every k the mass at ξ_{2k+1} is strictly below its value at every other radius from ξ_{2k} on and the mass at
ξ_{2k+2} strictly above its value at every other radius from ξ_{2k+1} on, m(ξ_{2k+1}) < √(2/π) < m(ξ_{2k}),
and m(s) tends to √(2/π) as s tends to infinity. -/
theorem bonnor_ebert_all_extrema (w φ : ℝ → ℝ)
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
  Work.Math.BEAllMain.main w φ hw hφ0 hφ h0

end Work.Math.BonnorEbertAll

#print axioms Work.Math.BonnorEbertAll.bonnor_ebert_all_extrema
