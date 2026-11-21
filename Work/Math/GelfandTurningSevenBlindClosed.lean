import Mathlib
import Work.Math.GelfandTurningValuesSeven

/-! Blind restatement of `Work.Math.GelfandTurningValuesSeven.gelfand_turning_values_seven` (run 2026-11-21T1028Z;
Sonnet, brief `runs/2026-11-21T1028Z/blind7/BRIEF.md`, output `runs/2026-11-21T1028Z/blind7/GelfandTurningSevenBlind.lean`,
copied verbatim below except the import and the namespace), closed in Lean from the program's statement. The blind
reading packs the solution class in a predicate, takes a two-sided derivative of φ for s > 0 (a stronger hypothesis
than the program's derivative within [0, ∞)) and states the conclusion with closed intervals; both are reduced to the
program's form. -/

namespace Work.Math.GelfandTurningSevenBlindClosed

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
  obtain ⟨hw0, hwd, hφc, hφd⟩ := h
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hφd s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ζ, hm, ht, a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, f1, f2, g1, g2, k1, k2, -, -, -, -, hlim, hinc0,
    hanti, hmono⟩ :=
    Work.Math.GelfandTurningValuesSeven.gelfand_turning_values_seven w φ (fun s hs => hwd s hs) hφc hφ' hw0
  exact ⟨ζ, hm, ht, hinc0, hanti, hmono, hlim, ⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩,
    ⟨g1, g2⟩, ⟨k1, k2⟩⟩

end Work.Math.GelfandTurningSevenBlindClosed
