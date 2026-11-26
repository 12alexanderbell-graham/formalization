import Mathlib
import Work.Math.GelfandTurningDecay

/-! Blind restatement of `Work.Math.GelfandTurningDecay.gelfand_turning_decay` (run 2026-11-26T1028Z;
Sonnet, brief `runs/2026-11-26T1028Z/blind/BRIEF.md`, output `runs/2026-11-26T1028Z/blind/GelfandTurningDecayBlind.lean`,
copied verbatim below except the import, this comment, the namespace and the proof), closed in Lean from the program's
statement. The blind reading bundles the hypotheses in a structure, takes a two-sided derivative of φ for s > 0 (a
stronger hypothesis than the program's derivative within [0, ∞)), names the branch parameter, writes the windows with
`Icc`, the bounds with the constants themselves, and the limit of the deviation quotient as
-Real.exp (-Real.pi / Real.sqrt 7); each is reduced to the program's form. -/


open Filter Set Real Topology

namespace Work.Math.GelfandTurningDecayBlindClosed.GelfandBlind

/-- `w` is the regular solution of `w'' + (2/s) w' + e^w = 0`, `w(0) = 0`,
with first derivative `φ` (one-sided at `0`, continuous at `0`). -/
structure IsRegularSol (w φ : ℝ → ℝ) : Prop where
  w_zero : w 0 = 0
  hasDeriv : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt w (φ s) (Ici 0) s
  phi_cont : ContinuousWithinAt φ (Ici 0) 0
  phi_ode : ∀ s : ℝ, 0 < s → HasDerivAt φ (-(2 / s) * φ s - Real.exp (w s)) s

/-- Branch parameter `λ(s) = s² e^{w(s)}`. -/
noncomputable def lam (w : ℝ → ℝ) (s : ℝ) : ℝ := s ^ 2 * Real.exp (w s)

end Work.Math.GelfandTurningDecayBlindClosed.GelfandBlind

namespace Work.Math.GelfandTurningDecayBlindClosed

open Work.Math.GelfandTurningDecayBlindClosed.GelfandBlind in
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
  have hφ' : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (hw.phi_ode s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ζ, hm, ht, a1, a2, b1, b2, hmax0, hmin, hmax, h2, hlim, hinc0, hanti, hmono, hq, hr, hb, hd⟩ :=
    Work.Math.GelfandTurningDecay.gelfand_turning_decay w φ (fun s hs => hw.hasDeriv s hs) hw.phi_cont hφ'
      hw.w_zero
  refine ⟨ζ, hm, ht, ⟨a1, a2⟩, ⟨b1, b2⟩, fun s hs hne => hmax0 s hs hne,
    fun k => ⟨fun s hs hne => hmin k s hs hne, fun s hs hne => hmax k s hs hne⟩, h2, hlim, hinc0,
    hanti, hmono, ?_, hr, fun k hk => ⟨⟨(hb k hk).1, (hb k hk).2.1⟩, ⟨(hb k hk).2.2.1, (hb k hk).2.2.2⟩⟩, ?_⟩
  · simpa only [lam, neg_div] using hq
  · obtain ⟨c₁, c₂, q, hc₁, hc₂, hq0, hq, hd⟩ := hd
    intro n
    have qn : q ^ n ≤ (33 / 100 : ℝ) ^ n := pow_le_pow_left₀ hq0 hq n
    have qn0 : 0 ≤ q ^ n := pow_nonneg hq0 n
    obtain ⟨d1, d2⟩ := hd n
    simp only [lam, neg_div]
    constructor
    · nlinarith
    · nlinarith

end Work.Math.GelfandTurningDecayBlindClosed
