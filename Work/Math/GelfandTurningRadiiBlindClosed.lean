import Mathlib
import Work.Math.GelfandTurningRadii

/-! Blind restatement of `Work.Math.GelfandTurningRadii.gelfand_turning_radii` (run 2026-11-25T1028Z;
Sonnet, brief `runs/2026-11-25T1028Z/blind/BRIEF.md`, output `runs/2026-11-25T1028Z/blind/GelfandTurningRadiiBlind.lean`,
copied verbatim below except the import, the namespace and the proof), closed in Lean from the program's statement. The
blind reading takes a two-sided derivative of φ for s > 0 (a stronger hypothesis than the program's derivative within
[0, ∞)), names the branch parameter, writes the centre and the first turning value as membership in closed intervals,
and writes the limit of the deviation quotient as -Real.exp (-Real.pi / Real.sqrt 7); each is reduced to the
program's form. -/

open Filter Topology Set

namespace Work.Math.GelfandTurningRadiiBlindClosed

/-- The quantity `λ(s) = s² e^{w(s)}`. -/
noncomputable def gelfandLam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

theorem blind_gelfand_turning_radii
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hw : ∀ s, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Ici 0) 0)
    (hφ : ∀ s, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧ Tendsto ζ atTop atTop ∧
      StrictMonoOn (gelfandLam w) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (gelfandLam w) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (gelfandLam w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      (∀ k : ℕ, gelfandLam w (ζ (2 * k + 1)) < 2 ∧ 2 < gelfandLam w (ζ (2 * k))) ∧
      Tendsto (gelfandLam w) atTop (𝓝 2) ∧
      ζ 0 ∈ Icc (4.071496844 : ℝ) 4.071496845 ∧
      gelfandLam w (ζ 0) ∈ Icc (3.321992118 : ℝ) 3.321992119 ∧
      Tendsto (fun k : ℕ => (gelfandLam w (ζ (k + 1)) - 2) / (gelfandLam w (ζ k) - 2))
        atTop (𝓝 (-Real.exp (-Real.pi / Real.sqrt 7))) ∧
      -- (i)
      Tendsto (fun k : ℕ => ζ (k + 1) / ζ k) atTop (𝓝 (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      -- (ii)
      (∀ k : ℕ, 6 ≤ k →
        10.3 ≤ ζ (k + 1) / ζ k ∧ ζ (k + 1) / ζ k ≤ 11.2 ∧
        -0.33 ≤ (gelfandLam w (ζ (k + 1)) - 2) / (gelfandLam w (ζ k) - 2) ∧
        (gelfandLam w (ζ (k + 1)) - 2) / (gelfandLam w (ζ k) - 2) ≤ -0.28) := by
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hφ s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ζ, hm, ht, a1, a2, b1, b2, -, -, -, h2, hlim, hinc0, hanti, hmono, hq, hr, hb⟩ :=
    Work.Math.GelfandTurningRadii.gelfand_turning_radii w φ (fun s hs => hw s hs) hφ0 hφ' hw0
  rw [neg_div]
  exact ⟨ζ, hm, ht, hinc0, hanti, hmono, h2, hlim, ⟨a1, a2⟩, ⟨b1, b2⟩, hq, hr, hb⟩

end Work.Math.GelfandTurningRadiiBlindClosed
