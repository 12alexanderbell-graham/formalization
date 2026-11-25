
namespace BlindTest
open Filter Topology Set

def IsRegularSolution (w φ : ℝ → ℝ) : Prop :=
  w 0 = 0 ∧
  (∀ s : ℝ, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s) ∧
  ContinuousWithinAt φ (Ici 0) 0 ∧
  (∀ s : ℝ, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s)

noncomputable def lam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

theorem blind_gelfand_turning_ratio (w φ : ℝ → ℝ) (h : IsRegularSolution w φ) :
    ∃ ζ : ℕ → ℝ,
      StrictMono ζ ∧
      Tendsto ζ atTop atTop ∧
      StrictMonoOn (lam w) (Icc 0 (ζ 0)) ∧
      (∀ k : ℕ,
        StrictAntiOn (lam w) (Icc (ζ (2 * k)) (ζ (2 * k + 1))) ∧
        StrictMonoOn (lam w) (Icc (ζ (2 * k + 1)) (ζ (2 * k + 2))) ∧
        lam w (ζ (2 * k + 1)) < 2 ∧ 2 < lam w (ζ (2 * k))) ∧
      Tendsto (lam w) atTop (𝓝 2) ∧
      ζ 0 ∈ Icc (4.071496844 : ℝ) 4.071496845 ∧
      lam w (ζ 0) ∈ Icc (3.321992118 : ℝ) 3.321992119 ∧
      Tendsto (fun k : ℕ => (lam w (ζ (k + 1)) - 2) / (lam w (ζ k) - 2)) atTop
        (𝓝 (-Real.exp (-Real.pi / Real.sqrt 7))) := by
  obtain ⟨hw0, hwd, hφc, hφd⟩ := h
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hφd s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ζ, hm, ht, a1, a2, b1, b2, -, -, -, h2, hlim, hinc0, hanti, hmono, hq⟩ :=
    GTR.ratio_main w φ (fun s hs => hwd s hs) hφc hφ' hw0
  rw [neg_div]
  exact ⟨ζ, hm, ht, hinc0, fun k => ⟨hanti k, hmono k, (h2 k).1, (h2 k).2⟩, hlim, ⟨a1, a2⟩, ⟨b1, b2⟩, hq⟩

end BlindTest
