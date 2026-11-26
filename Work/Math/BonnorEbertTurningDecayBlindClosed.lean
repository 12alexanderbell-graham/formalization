import Mathlib
import Work.Math.BonnorEbertTurningDecay

/-! Blind restatement of `Work.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay` (run 2026-11-26T0428Z;
Sonnet, brief `runs/2026-11-26T0428Z/blind/BRIEF.md`, output `runs/2026-11-26T0428Z/blind/BonnorEbertTurningDecayBlind.lean`,
copied verbatim below except the import, this comment, the namespace and the proof), closed in Lean from the program's
statement. The blind reading names the mass and the singular mass, takes a two-sided derivative of φ for s > 0 (a
stronger hypothesis than the program's derivative within [0, ∞)), states the global maximum by `IsMaxOn`, and writes
the limit of the deviation quotient as -Real.exp (-Real.pi / Real.sqrt 7); each is reduced to the program's form. -/

open Filter Set Real

namespace Work.Math.BonnorEbertTurningDecayBlindClosed.BonnorEbertBlind

/-- Dimensionless pressure-confined mass `m(s) = s² (−φ(s)) e^{w(s)/2} / √(4π)`,
where `φ = w'`. -/
noncomputable def mass (w φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * (-φ s) * Real.exp (w s / 2) / Real.sqrt (4 * Real.pi)

/-- Mass of the singular isothermal sphere. -/
noncomputable def singularMass : ℝ := Real.sqrt (2 / Real.pi)

end Work.Math.BonnorEbertTurningDecayBlindClosed.BonnorEbertBlind

namespace Work.Math.BonnorEbertTurningDecayBlindClosed

open Work.Math.BonnorEbertTurningDecayBlindClosed.BonnorEbertBlind in
theorem blind_bonnor_ebert_turning_decay
    (w φ : ℝ → ℝ)
    (hw0 : w 0 = 0)
    (hwd : ∀ s ∈ Set.Ici (0 : ℝ), HasDerivWithinAt w (φ s) (Set.Ici (0 : ℝ)) s)
    (hφ0 : ContinuousWithinAt φ (Set.Ici (0 : ℝ)) 0)
    (hφd : ∀ s : ℝ, 0 < s →
      HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s) :
    ∃ ξ : ℕ → ℝ,
      StrictMono ξ ∧
      Tendsto ξ atTop atTop ∧
      -- monotonicity pattern
      StrictMonoOn (mass w φ) (Set.Icc 0 (ξ 0)) ∧
      (∀ k : ℕ, StrictAntiOn (mass w φ) (Set.Icc (ξ (2 * k)) (ξ (2 * k + 1)))) ∧
      (∀ k : ℕ, StrictMonoOn (mass w φ) (Set.Icc (ξ (2 * k + 1)) (ξ (2 * k + 2)))) ∧
      -- global / tail extremality
      IsMaxOn (mass w φ) (Set.Ici 0) (ξ 0) ∧
      (∀ k : ℕ, ∀ s ∈ Set.Ici (ξ (2 * k)), s ≠ ξ (2 * k + 1) →
        mass w φ (ξ (2 * k + 1)) < mass w φ s) ∧
      (∀ k : ℕ, ∀ s ∈ Set.Ici (ξ (2 * k + 1)), s ≠ ξ (2 * k + 2) →
        mass w φ s < mass w φ (ξ (2 * k + 2))) ∧
      -- comparison with the singular isothermal sphere
      (∀ k : ℕ, mass w φ (ξ (2 * k + 1)) < singularMass ∧
        singularMass < mass w φ (ξ (2 * k))) ∧
      Tendsto (mass w φ) atTop (nhds singularMass) ∧
      -- first maximum
      (6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515) ∧
      -- asymptotic ratios
      Tendsto (fun k : ℕ => ξ (k + 1) / ξ k) atTop
        (nhds (Real.exp (2 * Real.pi / Real.sqrt 7))) ∧
      Tendsto (fun k : ℕ =>
          (mass w φ (ξ (k + 1)) - singularMass) / (mass w φ (ξ k) - singularMass))
        atTop (nhds (-Real.exp (-Real.pi / Real.sqrt 7))) ∧
      -- uniform bounds from index 5
      (∀ k : ℕ, 5 ≤ k →
        (9.2 ≤ ξ (k + 1) / ξ k ∧ ξ (k + 1) / ξ k ≤ 12.9) ∧
        (-0.42 ≤ (mass w φ (ξ (k + 1)) - singularMass) / (mass w φ (ξ k) - singularMass) ∧
          (mass w φ (ξ (k + 1)) - singularMass) / (mass w φ (ξ k) - singularMass) ≤ -0.21)) ∧
      -- geometric decay of the errors
      (∀ n : ℕ,
        |ξ (n + 6) / ξ (n + 5) - Real.exp (2 * Real.pi / Real.sqrt 7)|
            ≤ (23 / 10 : ℝ) * (21 / 50 : ℝ) ^ n ∧
        |(mass w φ (ξ (n + 6)) - singularMass) / (mass w φ (ξ (n + 5)) - singularMass)
            - (-Real.exp (-Real.pi / Real.sqrt 7))|
            ≤ (3 / 20 : ℝ) * (21 / 50 : ℝ) ^ n) := by
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hφd s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ξ, hm, ht, a1, a2, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hr, hq, hb, hd⟩ :=
    Work.Math.BonnorEbertTurningDecay.bonnor_ebert_turning_decay w φ hwd hφ0 hφ' hw0
  refine ⟨ξ, hm, ht, hinc0, hanti, hmono, ?_, fun k s hs hne => hmin k s hs hne,
    fun k s hs hne => hmax k s hs hne, h2, hlim, ⟨a1, a2⟩, hr, ?_,
    fun k hk => ⟨⟨(hb k hk).1, (hb k hk).2.1⟩, ⟨(hb k hk).2.2.1, (hb k hk).2.2.2⟩⟩, ?_⟩
  · intro s hs
    show mass w φ s ≤ mass w φ (ξ 0)
    by_cases h : s = ξ 0
    · subst h; exact le_rfl
    · exact (hmax0 s hs h).le
  · simpa only [mass, singularMass, neg_div] using hq
  · obtain ⟨c₁, c₂, q, hc₁, hc₂, hq0, hq, hd⟩ := hd
    intro n
    have qn : q ^ n ≤ (21 / 50 : ℝ) ^ n := pow_le_pow_left₀ hq0 hq n
    have qn0 : 0 ≤ q ^ n := pow_nonneg hq0 n
    obtain ⟨d1, d2⟩ := hd n
    simp only [mass, singularMass, neg_div]
    constructor
    · nlinarith
    · nlinarith

end Work.Math.BonnorEbertTurningDecayBlindClosed
