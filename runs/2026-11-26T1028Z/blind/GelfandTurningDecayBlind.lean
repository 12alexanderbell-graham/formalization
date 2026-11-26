import Mathlib

open Filter Set Real Topology

namespace GelfandBlind

/-- `w` is the regular solution of `w'' + (2/s) w' + e^w = 0`, `w(0) = 0`,
with first derivative `φ` (one-sided at `0`, continuous at `0`). -/
structure IsRegularSol (w φ : ℝ → ℝ) : Prop where
  w_zero : w 0 = 0
  hasDeriv : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s
  phi_cont : ContinuousWithinAt φ (Ici 0) 0
  phi_ode : ∀ s : ℝ, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s

/-- Branch parameter `λ(s) = s² e^{w(s)}`. -/
noncomputable def lam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

end GelfandBlind

open GelfandBlind in
theorem blind_gelfand_turning_decay (w φ : ℝ → ℝ) (hw : IsRegularSol w φ) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧
      Tendsto ζ atTop atTop ∧
      ζ 0 ∈ Icc (4.071496844 : ℝ) 4.071496845 ∧
      lam w (ζ 0) ∈ Icc (3.321992118 : ℝ) 3.321992119 ∧
      (∀ s : ℝ, 0 ≤ s → s ≠ ζ 0 → lam w s < lam w (ζ 0)) ∧
      (∀ k : ℕ,
        (∀ s ∈ Ici (ζ (2 * k)), s ≠ ζ (2 * k + 1) → lam w (ζ (2 * k + 1)) < lam w s) ∧
        (∀ s ∈ Ici (ζ (2 * k + 1)), s ≠ ζ (2 * k + 2) → lam w s < lam w (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, lam w (ζ (2 * k + 1)) < 2 ∧ 2 < lam w (ζ (2 * k))) ∧
      Tendsto (lam w) atTop (nhds 2) ∧
      StrictMonoOn (lam w) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (lam w) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (lam w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      Tendsto (fun k : ℕ => (lam w (ζ (k + 1)) - 2) / (lam w (ζ k) - 2)) atTop
        (nhds (-Real.exp (-Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ => ζ (k + 1) / ζ k) atTop
        (nhds (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      (∀ k : ℕ, 6 ≤ k →
        ζ (k + 1) / ζ k ∈ Icc (10.3 : ℝ) 11.2 ∧
        (lam w (ζ (k + 1)) - 2) / (lam w (ζ k) - 2) ∈ Icc (-0.33 : ℝ) (-0.28)) ∧
      (∀ n : ℕ,
        |ζ (n + 7) / ζ (n + 6) - Real.exp (2 * Real.pi / Real.sqrt 7)|
            ≤ (47 / 100 : ℝ) * (33 / 100 : ℝ) ^ n ∧
        |(lam w (ζ (n + 7)) - 2) / (lam w (ζ (n + 6)) - 2)
            - (-Real.exp (-Real.pi / Real.sqrt 7))|
            ≤ (3 / 100 : ℝ) * (33 / 100 : ℝ) ^ n) := by
  sorry
