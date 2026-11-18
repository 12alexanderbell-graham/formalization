import Mathlib
import Work.Math.BonnorEbertCount
import Work.Math.BonnorEbertCountBlind

/-! Bonnor–Ebert sphere: the blind restatement
`Work.Math.BonnorEbertCountBlind.blind_bonnor_ebert_count` (solution class as a structure with the equation as
`HasDerivAt` at every s > 0, written `-(2 / s) * φ s - e^w`; N as the `encard` of `{s | 0 ≤ s ∧ mass = μ}`)
closed from the frozen headline `Work.Math.BonnorEbertCount.bonnor_ebert_count`: `HasDerivAt` gives the
one-sided derivative within [0, ∞), the right-hand sides agree by `neg_mul`, and the sets agree by definition.
Written by run 2026-11-18T1628Z. -/

namespace Work.Math.BonnorEbertCountBlindClosed
open Set Filter Topology Work.Math.BonnorEbertCountBlind

theorem blind_closed (w φ : ℝ → ℝ) (h : IsSolution w φ) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧ Tendsto ξ atTop atTop ∧
      (6.4507514 ≤ ξ 0 ∧ ξ 0 ≤ 6.4507515) ∧
      (1.1822265 ≤ mass w φ (ξ 0) ∧ mass w φ (ξ 0) ≤ 1.1822266) ∧
      (0.694366 ≤ mass w φ (ξ 1) ∧ mass w φ (ξ 1) ≤ 0.694367) ∧
      (0.8306 ≤ mass w φ (ξ 2) ∧ mass w φ (ξ 2) ≤ 0.8308) ∧
      (0.787992 ≤ mass w φ (ξ 3) ∧ mass w φ (ξ 3) ≤ 0.787995) ∧
      (0.80091 ≤ mass w φ (ξ 4) ∧ mass w φ (ξ 4) ≤ 0.800916) ∧
      Tendsto (fun k => mass w φ (ξ k)) atTop (nhds (Real.sqrt (2 / Real.pi))) ∧
      (∀ μ : ℝ, mass w φ (ξ 0) < μ → N w φ μ = 0) ∧
      N w φ (mass w φ (ξ 0)) = 1 ∧
      (∀ (k : ℕ) (μ : ℝ), mass w φ (ξ (2 * k + 2)) < μ → μ < mass w φ (ξ (2 * k)) →
        N w φ μ = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ k : ℕ, N w φ (mass w φ (ξ (2 * k + 2))) = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      (∀ μ : ℝ, 0 < μ → μ < mass w φ (ξ 1) → N w φ μ = 1) ∧
      (∀ k : ℕ, N w φ (mass w φ (ξ (2 * k + 1))) = ((2 * k + 2 : ℕ) : ℕ∞)) ∧
      (∀ (k : ℕ) (μ : ℝ), mass w φ (ξ (2 * k + 1)) < μ → μ < mass w φ (ξ (2 * k + 3)) →
        N w φ μ = ((2 * k + 3 : ℕ) : ℕ∞)) ∧
      N w φ (Real.sqrt (2 / Real.pi)) = ⊤ := by
  have hφ : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivWithinAt φ (-(2 / s * φ s) - Real.exp (w s)) (Ici 0) s := by
    intro s hs
    have := (h.ode s hs).hasDerivWithinAt (s := Ici 0)
    rwa [neg_mul] at this
  obtain ⟨ξ, hm, ht, a0, b0, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, hl, ca, cb, cc, cd, ce, cf, cg,
      ch⟩ := Work.Math.BonnorEbertCount.bonnor_ebert_count w φ (fun s hs => h.hasDeriv s hs)
      h.cont0 hφ h.w_zero
  exact ⟨ξ, hm, ht, ⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, hl, ca, cb, cc,
    cd, ce, cf, cg, ch⟩

end Work.Math.BonnorEbertCountBlindClosed
