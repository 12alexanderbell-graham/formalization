import Work.Math.GelfandTurningValuesFive

/-! Blind restatement of `Work.Math.GelfandTurningValuesFive.gelfand_turning_values_five` (run 2026-11-21T0428Z;
Sonnet, brief `runs/2026-11-21T0428Z/blind/BRIEF.md`, output `runs/2026-11-21T0428Z/blind/GelfandTurningFiveBlind.lean`,
copied verbatim below except the import and the namespace), closed in Lean from the program's statement. The blind
reading takes a two-sided derivative of φ for s > 0 (a stronger hypothesis than the program's derivative within
[0, ∞)) and states the conclusion with closed intervals; both are reduced to the program's form. -/

namespace Work.Math.GelfandTurningFiveBlindClosed

open Filter Set

/-- The quantity `λ(s) = s² e^{w(s)}`. -/
noncomputable def gelfandLam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

theorem blind_gelfand_turning_five
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hwd : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici (0 : ℝ)) s)
    (hφc : ContinuousWithinAt φ (Ici (0 : ℝ)) 0)
    (hφd : ∀ s : ℝ, 0 < s →
      HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧
      Tendsto ζ atTop atTop ∧
      StrictMonoOn (gelfandLam w) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (gelfandLam w) (Icc (ζ (2 * k)) (ζ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (gelfandLam w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2)))) ∧
      Tendsto (gelfandLam w) atTop (nhds 2) ∧
      ζ 0 ∈ Icc (4.071496844 : ℝ) 4.071496845 ∧
      gelfandLam w (ζ 0) ∈ Icc (3.321992118 : ℝ) 3.321992119 ∧
      gelfandLam w (ζ 1) ∈ Icc (1.664155 : ℝ) 1.664157 ∧
      gelfandLam w (ζ 2) ∈ Icc (2.10852 : ℝ) 2.10858 ∧
      gelfandLam w (ζ 3) ∈ Icc (1.967422 : ℝ) 1.967510 ∧
      gelfandLam w (ζ 4) ∈ Icc (2.009926 : ℝ) 2.010028 := by
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hφd s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ζ, hm, ht, a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, f1, f2, -, -, -, -, hlim, hinc0, hanti, hmono⟩ :=
    Work.Math.GelfandTurningValuesFive.gelfand_turning_values_five w φ (fun s hs => hwd s hs) hφc hφ' hw0
  exact ⟨ζ, hm, ht, hinc0, hanti, hmono, hlim, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩

end Work.Math.GelfandTurningFiveBlindClosed
