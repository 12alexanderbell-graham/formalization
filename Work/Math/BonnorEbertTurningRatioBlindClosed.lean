import Mathlib
import Work.Math.BonnorEbertTurningRatio

/-! Blind restatement of `Work.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio` (run 2026-11-25T1628Z;
Sonnet, brief `runs/2026-11-25T1628Z/blind/BRIEF.md`, output `runs/2026-11-25T1628Z/blind/BonnorEbertTurningRatioBlind.lean`,
copied verbatim below except the import, the namespace and the proof), closed in Lean from the program's statement. The
blind reading names the mass and the singular value, takes a two-sided derivative of φ for s > 0 (a stronger
hypothesis than the program's derivative within [0, ∞)), states the global maximum with a weak inequality, writes the
window of the first radius as membership of a closed interval and the last limit as -Real.exp (-Real.pi / Real.sqrt 7);
each is reduced to the program's form. -/

open Filter Topology Set

namespace Work.Math.BonnorEbertTurningRatioBlindClosed

noncomputable section

/-- Dimensionless pressure-confined mass at radius `s`, for a solution `w` with derivative `φ`. -/
def beMass (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

/-- Mass of the singular isothermal sphere. -/
def singularMass : ℝ := Real.sqrt (2 / Real.pi)

theorem blind_bonnor_ebert_turning_ratio
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hw : ∀ s, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ξ : ℕ → ℝ,
      StrictMono ξ ∧
      Tendsto ξ atTop atTop ∧
      StrictMonoOn (beMass w φ) (Icc 0 (ξ 0)) ∧
      (∀ k, StrictAntiOn (beMass w φ) (Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k, StrictMonoOn (beMass w φ) (Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      (∀ s, 0 ≤ s → beMass w φ s ≤ beMass w φ (ξ 0)) ∧
      (∀ k, ∀ s, ξ (2 * k) ≤ s → s ≠ ξ (2 * k + 1) →
        beMass w φ (ξ (2 * k + 1)) < beMass w φ s) ∧
      (∀ k, ∀ s, ξ (2 * k + 1) ≤ s → s ≠ ξ (2 * k + 2) →
        beMass w φ s < beMass w φ (ξ (2 * k + 2))) ∧
      (∀ k, beMass w φ (ξ (2 * k + 1)) < singularMass ∧
            singularMass < beMass w φ (ξ (2 * k))) ∧
      Tendsto (beMass w φ) atTop (𝓝 singularMass) ∧
      ξ 0 ∈ Icc (6.4507514 : ℝ) 6.4507515 ∧
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop
        (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
          (beMass w φ (ξ (k + 1)) - singularMass) / (beMass w φ (ξ k) - singularMass))
        atTop (𝓝 (-Real.exp (-Real.pi / Real.sqrt 7))) := by
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hφ s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ξ, hm, ht, a1, a2, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hr, hq⟩ :=
    Work.Math.BonnorEbertTurningRatio.bonnor_ebert_turning_ratio w φ (fun s hs => hw s hs) hφ0 hφ' hw0
  rw [neg_div]
  refine ⟨ξ, hm, ht, hinc0, hanti, hmono, ?_, fun k s hs hne => hmin k s hs hne,
    fun k s hs hne => hmax k s hs hne, h2, hlim, ⟨a1, a2⟩, hr, hq⟩
  intro s hs
  by_cases h : s = ξ 0
  · rw [h]
  · exact (hmax0 s hs h).le

end

end Work.Math.BonnorEbertTurningRatioBlindClosed
