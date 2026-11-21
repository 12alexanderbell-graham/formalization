import Mathlib

open Filter Topology Set Real

/-- Regular solution of `w'' + (2/s) w' + e^w = 0`, `w(0) = 0`, with `φ = w'`. -/
def IsRegularIsothermal (w φ : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧
  (∀ s : ℝ, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici (0 : ℝ)) s) ∧
  ContinuousWithinAt φ (Ici (0 : ℝ)) 0 ∧
  (∀ s : ℝ, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s)

theorem blind_gelfand_turning_seven (w φ : ℝ → ℝ) (h : IsRegularIsothermal w φ) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      StrictMonoOn (fun s : ℝ => s ^ 2 * Real.exp (w s)) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (fun s : ℝ => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (fun s : ℝ => s ^ 2 * Real.exp (w s)) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      Tendsto (fun s : ℝ => s ^ 2 * Real.exp (w s)) atTop (𝓝 2) ∧
      ζ 0 ∈ Icc (4.071496844 : ℝ) 4.071496845 ∧
      (ζ 0) ^ 2 * Real.exp (w (ζ 0)) ∈ Icc (3.321992118 : ℝ) 3.321992119 ∧
      (ζ 1) ^ 2 * Real.exp (w (ζ 1)) ∈ Icc (1.664155 : ℝ) 1.664157 ∧
      (ζ 2) ^ 2 * Real.exp (w (ζ 2)) ∈ Icc (2.10852 : ℝ) 2.10858 ∧
      (ζ 3) ^ 2 * Real.exp (w (ζ 3)) ∈ Icc (1.967422 : ℝ) 1.967510 ∧
      (ζ 4) ^ 2 * Real.exp (w (ζ 4)) ∈ Icc (2.009926 : ℝ) 2.010028 ∧
      (ζ 5) ^ 2 * Real.exp (w (ζ 5)) ∈ Icc (1.996901 : ℝ) 1.997023 ∧
      (ζ 6) ^ 2 * Real.exp (w (ζ 6)) ∈ Icc (2.000873 : ℝ) 2.000980 := by
  sorry
