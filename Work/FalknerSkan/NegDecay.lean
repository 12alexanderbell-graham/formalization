import Mathlib
import Work.FalknerSkan.NegCore

/-!
# Falkner–Skan with adverse pressure gradient (β < 0): uniqueness in the decay class

Frozen in run 2026-11-09T0828Z (statements first, proofs follow). Equation in the program's β-form:
f''' + f f'' + β (1 − f'²) = 0 on [0, ∞), written as the first-order system f' = p, p' = q,
q' = −f q − β (1 − p²) with one-sided derivatives at 0; wall conditions f(0) = 0, p(0) = 0.

The class: q > 0 on [0, ∞) (monotone velocity) and, for every M, eventually M (1 − p) ≤ q
(the velocity approaches 1 faster than any exponential). For β < 0 the class matters:
uniqueness in 0 ≤ f' ≤ 1 alone is false (a continuum of solutions with algebraic approach,
`runs/2026-11-09T0428Z/research/fs_negative_beta.md` §1.5, referee `runs/2026-11-09T0828Z/referee/REPORT.md`).
-/

namespace Work.FalknerSkan.NegDecay

open Set Filter Topology

/-- Falkner–Skan with β < 0: if (f, p, q) solves f''' + f f'' + β(1 − f'²) = 0 on [0, ∞) with
f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, eventually M (1 − p) ≤ q, and
(f₂, p₂, q₂) solves the same problem with q₂ > 0 on [0, ∞) (no condition on its approach), then
q₂(0) ≤ q(0). -/
theorem fs_neg_decay_max_shear (β : ℝ) (hβ : β < 0) (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η) :
    q₂ 0 ≤ q 0 := by
  have hc : 0 < Real.sqrt (-β) := Real.sqrt_pos.2 (by linarith)
  have hK : (0 : ℝ) < 1 / (-β) := one_div_pos.2 (by linarith)
  have h := Work.FalknerSkan.NegUPrime.u_prime hK
    (Work.FalknerSkan.NegCore.toSol hβ hf hp hq hf0 hp0 hlim hpos)
    (Work.FalknerSkan.NegCore.toSol hβ hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂)
    (Work.FalknerSkan.NegCore.toDec hβ hdec)
  simp only [zero_div] at h
  exact (div_le_div_iff_of_pos_right hc).1 h

/-- Falkner–Skan with β < 0: two solutions of f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), each with
f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, eventually M (1 − p) ≤ q, agree:
f η = f₂ η, p η = p₂ η and q η = q₂ η for every η ≥ 0. -/
theorem fs_neg_decay_equal (β : ℝ) (hβ : β < 0) (f p q f₂ p₂ q₂ : ℝ → ℝ)
    (hf : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η)
    (hp : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η)
    (hq : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - β * (1 - p η ^ 2)) (Ici 0) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hlim : Tendsto p atTop (𝓝 1))
    (hpos : ∀ η ∈ Ici (0 : ℝ), 0 < q η)
    (hdec : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η)
    (hf₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η)
    (hp₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η)
    (hq₂ : ∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - β * (1 - p₂ η ^ 2)) (Ici 0) η)
    (hf₂0 : f₂ 0 = 0) (hp₂0 : p₂ 0 = 0) (hlim₂ : Tendsto p₂ atTop (𝓝 1))
    (hpos₂ : ∀ η ∈ Ici (0 : ℝ), 0 < q₂ η)
    (hdec₂ : ∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p₂ η) ≤ q₂ η) :
    ∀ η ∈ Ici (0 : ℝ), f η = f₂ η ∧ p η = p₂ η ∧ q η = q₂ η := by
  have h1 := fs_neg_decay_max_shear β hβ f p q f₂ p₂ q₂ hf hp hq hf0 hp0 hlim hpos hdec
    hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂
  have h2 := fs_neg_decay_max_shear β hβ f₂ p₂ q₂ f p q hf₂ hp₂ hq₂ hf₂0 hp₂0 hlim₂ hpos₂ hdec₂
    hf hp hq hf0 hp0 hlim hpos
  exact Work.FalknerSkan.NegCore.eq_of_startb hf hp hq hf₂ hp₂ hq₂ (by rw [hf0, hf₂0])
    (by rw [hp0, hp₂0]) (le_antisymm h2 h1)

end Work.FalknerSkan.NegDecay
