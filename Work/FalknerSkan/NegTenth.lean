import Mathlib
import Work.FSNeg.NAssemble
import Work.FSNeg.NSlowHalf
import Work.FSNeg.NSlow34
import Work.FSNeg.NOver11

/-!
# Falkner–Skan β = −1/10 (adverse pressure gradient): existence in the decay class, and
# non-uniqueness without the decay condition

Frozen in run 2026-11-09T0828Z (statements first, proofs follow). Program β-form with β = −1/10:
f' = p, p' = q, q' = −f q − β (1 − p²), one-sided derivatives at 0, f(0) = 0, p(0) = 0.
Plan: `runs/2026-11-09T0428Z/research/fs_negative_beta.md` §3 (events Slow/Over at the scaled
coefficient K = 10, certified cells), referee `runs/2026-11-09T0828Z/referee/REPORT.md`.
-/

namespace Work.FalknerSkan.NegTenth

open Set Filter Topology

/-- Falkner–Skan with β = −1/10: there is a solution (f, p, q) of f''' + f f'' + β(1 − f'²) = 0
on [0, ∞) with f(0) = 0, p(0) = 0, p → 1, q > 0 on [0, ∞) and, for every M, eventually
M (1 − p) ≤ q. -/
theorem fs_neg_tenth_exists_decay :
    ∃ f p q : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η) ∧
      (∀ M : ℝ, ∀ᶠ η in atTop, M * (1 - p η) ≤ q η) := by
  exact Work.FSNeg.NAssemble.core_exists ⟨9 / 8, by norm_num, fun Y hY h0 => Work.FSNeg.NSlow34.chainC hY h0⟩
    ⟨5 / 4, by norm_num, fun Y hY h0 => Work.FSNeg.NOver11.chainC hY h0⟩

/-- Falkner–Skan with β = −1/10: there are two solutions (f, p, q) and (f₂, p₂, q₂) of
f''' + f f'' + β(1 − f'²) = 0 on [0, ∞), both with f(0) = 0, p(0) = 0, p → 1, q > 0 and
0 ≤ p ≤ 1 on [0, ∞), and eventually q < 3 (1 − p), whose values q(0) and q₂(0) differ. -/
theorem fs_neg_tenth_not_unique :
    ∃ f p q f₂ p₂ q₂ : ℝ → ℝ,
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(f η * q η) - (-1 / 10) * (1 - p η ^ 2)) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f₂ (p₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p₂ (q₂ η) (Ici 0) η) ∧
      (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q₂ (-(f₂ η * q₂ η) - (-1 / 10) * (1 - p₂ η ^ 2)) (Ici 0) η) ∧
      f 0 = 0 ∧ p 0 = 0 ∧ f₂ 0 = 0 ∧ p₂ 0 = 0 ∧
      Tendsto p atTop (𝓝 1) ∧ Tendsto p₂ atTop (𝓝 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q η ∧ 0 ≤ p η ∧ p η ≤ 1) ∧
      (∀ η ∈ Ici (0 : ℝ), 0 < q₂ η ∧ 0 ≤ p₂ η ∧ p₂ η ≤ 1) ∧
      (∀ᶠ η in atTop, q η < 3 * (1 - p η)) ∧ (∀ᶠ η in atTop, q₂ η < 3 * (1 - p₂ η)) ∧
      q 0 ≠ q₂ 0 := by
  exact Work.FSNeg.NAssemble.core_not_unique
    ⟨5 / 4, by norm_num, fun Y hY h0 => Work.FSNeg.NSlowHalf.chainC hY h0⟩
    ⟨9 / 8, by norm_num, fun Y hY h0 => Work.FSNeg.NSlow34.chainC hY h0⟩

end Work.FalknerSkan.NegTenth
