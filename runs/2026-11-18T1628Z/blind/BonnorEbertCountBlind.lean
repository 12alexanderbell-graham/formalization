import Mathlib

open Filter Set Real

namespace BlindBE

/-- Dimensionless mass of the isothermal sphere cut at radius `s`. -/
noncomputable def mass (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

/-- Number of radii `s ≥ 0` with mass `μ`. -/
noncomputable def N (w φ : ℝ → ℝ) (μ : ℝ) : ℕ∞ :=
  Set.encard {s : ℝ | 0 ≤ s ∧ mass w φ s = μ}

/-- `w` is the regular solution of `w'' + (2/s) w' + e^w = 0`, `w(0)=0`, `w'(0)=0`
(here `φ = w'`, and `φ(0)=0` is forced by continuity at 0 together with the ODE). -/
structure IsSolution (w φ : ℝ → ℝ) : Prop where
  w_zero : w 0 = 0
  hasDeriv : ∀ s, 0 ≤ s → HasDerivWithinAt w (φ s) (Set.Ici 0) s
  cont0 : ContinuousWithinAt φ (Set.Ici 0) 0
  ode : ∀ s, 0 < s →
    HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s

theorem blind_bonnor_ebert_count (w φ : ℝ → ℝ) (h : IsSolution w φ) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      (6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515) ∧
      (1.1822265 ≤ mass w φ (ξ 0) ∧ mass w φ (ξ 0) ≤ 1.1822266) ∧
      (0.694366 ≤ mass w φ (ξ 1) ∧ mass w φ (ξ 1) ≤ 0.694367) ∧
      (0.8306 ≤ mass w φ (ξ 2) ∧ mass w φ (ξ 2) ≤ 0.8308) ∧
      (0.787992 ≤ mass w φ (ξ 3) ∧ mass w φ (ξ 3) ≤ 0.787995) ∧
      (0.80091 ≤ mass w φ (ξ 4) ∧ mass w φ (ξ 4) ≤ 0.800916) ∧
      Tendsto (fun k => mass w φ (ξ k)) atTop (nhds (Real.sqrt (2 / Real.pi))) ∧
      -- (a)
      (∀ μ : ℝ, mass w φ (ξ 0) < μ → N w φ μ = 0) ∧
      -- (b)
      N w φ (mass w φ (ξ 0)) = 1 ∧
      -- (c)
      (∀ (k : ℕ) (μ : ℝ), mass w φ (ξ (2 * k + 2)) < μ → μ < mass w φ (ξ (2 * k)) →
        N w φ μ = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      -- (d)
      (∀ k : ℕ, N w φ (mass w φ (ξ (2 * k + 2))) = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      -- (e)
      (∀ μ : ℝ, 0 < μ → μ < mass w φ (ξ 1) → N w φ μ = 1) ∧
      -- (f)
      (∀ k : ℕ, N w φ (mass w φ (ξ (2 * k + 1))) = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      -- (g)
      (∀ (k : ℕ) (μ : ℝ), mass w φ (ξ (2 * k + 1)) < μ → μ < mass w φ (ξ (2 * k + 3)) →
        N w φ μ = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      -- (h)
      N w φ (Real.sqrt (2 / Real.pi)) = ⊤ := by
  sorry

end BlindBE
