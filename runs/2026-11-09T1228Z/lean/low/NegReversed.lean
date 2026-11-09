import Mathlib
import Work.FSNeg.LAssemble
import Work.FSNeg.LOver
import Work.FSNeg.LSlow
import Work.FSNeg.LTube
import Work.FSNeg.NWindow
import Work.FalknerSkan.NegTenth

/-!
# Falkner–Skan β = −1/10 (adverse pressure gradient): the reversed-flow solution, and two solutions
# in the decay class

Program β-form with β = −1/10: f' = p, p' = q, q' = −f q − β (1 − p²), one-sided derivatives at 0,
f(0) = 0, p(0) = 0, p → 1. Route: certified chains in scaled variables (K = 10) — Over at
−0.4444461497, the lower Slow event at −0.4444461493 and a tube around the window on [0, 3/2]
(`runs/2026-11-09T1228Z/scripts/make_lower.sh`) — the supremum argument
(`Work.FSNeg.LAssemble.core_lower`) and scaling by √10.
-/

namespace Work.FalknerSkan.NegReversed

open Set Filter Topology

theorem tube : Work.FSNeg.LAssemble.TubeTo (-4444461497 / 10000000000) (-4444461493 / 10000000000) := by
  intro α hα Y hY h0
  have hα' : |α - -4444461495 / 10000000000| ≤ 1 / 5000000000 := by
    rw [abs_le]; constructor <;> linarith [hα.1, hα.2]
  have := Work.FSNeg.LTube.chainC (Y := Y) (by norm_num at hY ⊢; exact hY) h0 hα'
  norm_num at this ⊢
  exact this

theorem lo_bound : (-0.1405462131 : ℝ) < -4444461497 / 10000000000 / Real.sqrt 10 := by
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  rw [lt_div_iff₀ hc]
  have := Work.FSNeg.NWindow.sqrt10_gt
  nlinarith

theorem hi_bound : -4444461493 / 10000000000 / Real.sqrt 10 < (-0.1405462129 : ℝ) := by
  have hc : 0 < Real.sqrt 10 := Real.sqrt_pos.2 (by norm_num)
  rw [div_lt_iff₀ hc]
  have := Work.FSNeg.NWindow.sqrt10_lt
  nlinarith

/-- Falkner–Skan with β = −1/10: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q, whose wall value satisfies −0.1405462131 < q(0) < −0.1405462129 (reversed flow
at the wall). -/
theorem fs_neg_tenth_reversed :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      -0.1405462131 < q 0 ∧ q 0 < -0.1405462129 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8, w1, w2⟩ :=
    Work.FSNeg.LAssemble.core_lower (by norm_num)
      ⟨15 / 4, by norm_num, fun _ hY h0 => Work.FSNeg.LOver.chainC hY h0⟩
      ⟨4, by norm_num, fun _ hY h0 => Work.FSNeg.LSlow.chainC hY h0⟩ tube
  exact ⟨f, p, q, a1, a2, a3, a4, a5, a6,
    fun η hη => ⟨by linarith [(a7 η hη).1], (a7 η hη).2.le⟩, a8, lo_bound.trans w1, w2.trans hi_bound⟩

/-- Falkner–Skan with β = −1/10: there are two solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, −1 ≤ p ≤ 1 on
[0, ∞) and, for every M, eventually M (1 − p) ≤ q, whose values q(0) and q₂(0) differ. -/
theorem fs_neg_tenth_two_decay :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1 / 10) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1) ∧ (∀ η ∈ Ici (0 : ℝ), -1 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) ∧
      q 0 ≠ q₂ 0 := by
  obtain ⟨f, p, q, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    Work.FalknerSkan.NegTenth.fs_neg_tenth_exists_decay
  obtain ⟨f₂, p₂, q₂, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := fs_neg_tenth_reversed
  -- the attached solution: q > 0, so p increases from 0 to its limit 1
  have hb : ∀ η ∈ Ici (0 : ℝ), -1 ≤ p η ∧ p η ≤ 1 := by
    intro η hη
    have hη0 : (0 : ℝ) ≤ η := hη
    have h1 : p 0 ≤ p η := Checked.FalknerSkan.LimitCore.mono a2 (le_refl (0 : ℝ)) (b := η)
      (fun x hx => (a7 x hx.1.le).le) ⟨le_rfl, hη0⟩ ⟨hη0, le_rfl⟩ hη0
    have h2 : p η ≤ 1 := by
      refine ge_of_tendsto a6 ?_
      filter_upwards [eventually_ge_atTop η] with t ht
      exact Checked.FalknerSkan.LimitCore.mono a2 hη0 (b := t)
        (fun x hx => (a7 x (hη0.trans hx.1.le)).le) ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    constructor <;> linarith
  have hq : q 0 ≠ q₂ 0 := by
    have := a7 0 (mem_Ici.2 le_rfl)
    intro h; rw [h] at this; linarith [b9]
  exact ⟨f, p, q, f₂, p₂, q₂, a1, a2, a3, b1, b2, b3, a4, a5, b4, b5, a6, b6, hb, b7, a8, b8, hq⟩

end Work.FalknerSkan.NegReversed
