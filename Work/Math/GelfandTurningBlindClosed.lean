import Work.Math.GelfandTurningValues

/-! Blind restatement of `Work.Math.GelfandTurningValues.gelfand_turning_values` (run 2026-11-20T1028Z; Sonnet,
brief `runs/2026-11-20T1028Z/blind/BRIEF.md`, output `runs/2026-11-20T1028Z/blind/GelfandTurningBlind.lean`,
copied verbatim below except the namespace), closed in Lean from the program's statement. The blind reading takes
a two-sided derivative of φ for s > 0 (a stronger hypothesis than the program's derivative within [0, ∞)) and
states the conclusion with closed intervals; both are reduced to the program's form. -/

namespace Work.Math.GelfandTurningBlindClosed
open Filter Set Real Topology

/-- The quantity `λ(s) = s² e^{w(s)}`. -/
noncomputable def gelfandLam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

theorem blind_gelfand_turning (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hw : ∀ s, 0 ≤ s → HasDerivWithinAt w (φ s) (Set.Ici 0) s)
    (hφ0 : ContinuousWithinAt φ (Set.Ici 0) 0)
    (hφ : ∀ s, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧
      Tendsto ζ atTop atTop ∧
      StrictMonoOn (gelfandLam w) (Set.Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (gelfandLam w) (Set.Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (gelfandLam w) (Set.Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      Tendsto (gelfandLam w) atTop (nhds 2) ∧
      ζ 0 ∈ Set.Icc (4.071496844 : ℝ) 4.071496845 ∧
      gelfandLam w (ζ 0) ∈ Set.Icc (3.321992118 : ℝ) 3.321992119 ∧
      gelfandLam w (ζ 1) ∈ Set.Icc (1.664155 : ℝ) 1.664157 ∧
      gelfandLam w (ζ 2) ∈ Set.Icc (2.10852 : ℝ) 2.10858 ∧
      gelfandLam w (ζ 3) ∈ Set.Icc (1.9637 : ℝ) 1.9707 := by
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hφ s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ζ, hm, ht, a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, -, -, -, -, hlim, hinc0, hanti, hmono⟩ :=
    Work.Math.GelfandTurningValues.gelfand_turning_values w φ (fun s hs => hw s hs) hφ0 hφ' hw0
  exact ⟨ζ, hm, ht, hinc0, hanti, hmono, hlim, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩⟩

end Work.Math.GelfandTurningBlindClosed
