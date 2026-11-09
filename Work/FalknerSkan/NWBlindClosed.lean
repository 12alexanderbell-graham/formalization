import Mathlib
import Work.FalknerSkan.NegWindow

/-!
# Falkner–Skan β = −1/10, ten-decimal window: the blind restatement, closed (run 2026-11-09T1228Z)

The definitions and the theorems `window`, `monotone_lt` are the blind restater's text (Sonnet, from
the claims in words only; `runs/2026-11-09T1228Z/blind/NegWindowBlind.lean`, brief next to it), copied
verbatim with the placeholder proofs replaced by proofs from
`Work.FalknerSkan.NegWindow.fs_neg_tenth_window` and `fs_neg_tenth_monotone_lt`; `toSys` is program
text, not blind text.
-/

namespace Blind.NegWindow

open Set Filter Topology

/-- First, second, third derivatives of `f` on the half-line `[0,∞)` (one-sided at 0). -/
noncomputable def d1 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin f (Ici 0)
noncomputable def d2 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d1 f) (Ici 0)
noncomputable def d3 (f : ℝ → ℝ) : ℝ → ℝ := derivWithin (d2 f) (Ici 0)

/-- `f` solves the Falkner–Skan boundary-value problem with parameter `β`. -/
structure IsSolution (β : ℝ) (f : ℝ → ℝ) : Prop where
  smooth : ContDiffOn ℝ 3 f (Ici 0)
  ode : ∀ η, 0 ≤ η → d3 f η + f η * d2 f η + β * (1 - (d1 f η) ^ 2) = 0
  f0 : f 0 = 0
  f'0 : d1 f 0 = 0
  limit : Tendsto (d1 f) atTop (𝓝 1)

/-- From the blind `IsSolution β` to the program's first-order system (program lemma, not part of
the blind text; pattern of `Work.FalknerSkan.BBlindClosed.toSys`). -/
theorem toSys {β : ℝ} {f : ℝ → ℝ} (h : IsSolution β f) :
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt f (d1 f x) (Ici 0) x) ∧
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (d1 f) (d2 f x) (Ici 0) x) ∧
    (∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (d2 f)
      (-(f x * d2 f x) - β * (1 - d1 f x ^ 2)) (Ici 0) x) ∧
    f 0 = 0 ∧ d1 f 0 = 0 ∧ Tendsto (d1 f) atTop (𝓝 1) := by
  have hu : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have c1 : ContDiffOn ℝ 2 (d1 f) (Ici 0) := h.smooth.derivWithin hu (by norm_num)
  have c2 : ContDiffOn ℝ 1 (d2 f) (Ici 0) := c1.derivWithin hu (by norm_num)
  refine ⟨fun x hx => ((h.smooth.differentiableOn (by norm_num)) x hx).hasDerivWithinAt,
    fun x hx => ((c1.differentiableOn (by norm_num)) x hx).hasDerivWithinAt,
    fun x hx => (((c2.differentiableOn (by norm_num)) x hx).hasDerivWithinAt).congr_deriv
      (by have := h.ode x hx; unfold d3 at this; linarith), h.f0, h.f'0, h.limit⟩

theorem window (f : ℝ → ℝ) (hf : IsSolution (-1/10) f)
    (hpos : ∀ η, 0 ≤ η → 0 < d2 f η)
    (hdecay : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - d1 f η) ≤ d2 f η) :
    (3192697598 / 10 ^ 10 : ℝ) < d2 f 0 ∧ d2 f 0 < 3192697599 / 10 ^ 10 := by
  obtain ⟨A, B, C, E0, E1, L⟩ := toSys hf
  have W := Work.FalknerSkan.NegWindow.fs_neg_tenth_window _ _ _ A B
    (fun x hx => (C x hx).congr_deriv (by ring)) E0 E1 L hpos hdecay
  constructor <;> norm_num at W ⊢ <;> linarith [W.1, W.2]

theorem monotone_lt (f : ℝ → ℝ) (hf : IsSolution (-1/10) f)
    (hpos : ∀ η, 0 ≤ η → 0 < d2 f η) :
    d2 f 0 < 3192697599 / 10 ^ 10 := by
  obtain ⟨A, B, C, E0, E1, L⟩ := toSys hf
  have W := Work.FalknerSkan.NegWindow.fs_neg_tenth_monotone_lt _ _ _ A B
    (fun x hx => (C x hx).congr_deriv (by ring)) E0 E1 L hpos
  norm_num at W ⊢; linarith

end Blind.NegWindow
