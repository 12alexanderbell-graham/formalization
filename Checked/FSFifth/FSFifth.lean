import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Checked.FSFifth.F5UData
import Checked.FSFifth.F5OData
import Checked.FSFifth.F5ExAssemble

/-! Falkner–Skan one-fifth row, the Falkner–Skan equation with pressure-gradient coefficient one fifth after the similarity scaling by the square root of that coefficient: the two certified shooting events and existence. Module `FSFifth`, promoted from `Work/FSFifth/FSFifth.lean`. -/

namespace Checked.FSFifth
open Set Filter Topology

/-- Falkner–Skan β = 1/5 in scaled form (coefficient 5), undershoot: for every S ≥ 4 and every solution of
f''' + 5 f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−5 f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.5355261734, there is
η in (0, 4] with q(η) < 0 and p < 1 on [0, η]. -/
theorem k5_under (S : ℝ) (hS : 4 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(5 * f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.5355261734) :
    ∃ η ∈ Ioc (0 : ℝ) 4, q η < 0 ∧ ∀ s ∈ Icc 0 η, p s < 1 := by
  have hsub : Icc (0 : ℝ) 4 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hq', hp'⟩ := Checked.FSFifth.F5UData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨4, ⟨by norm_num, le_rfl⟩, hq', hp'⟩

/-- Falkner–Skan β = 1/5 in scaled form (coefficient 5), overshoot: for every S ≥ 4 and every solution of
f''' + 5 f f'' + 1 − f'² = 0 on [0, S] (f has derivative p, p has derivative q, q has derivative
−5 f q − 1 + p², within [0, S]) with f(0) = 0, p(0) = 0 and q(0) = 1.5355261735, there is
η in (0, 4] with p(η) > 1 and q > 0 on [0, η]. -/
theorem k5_over (S : ℝ) (hS : 4 ≤ S) (f p q : ℝ → ℝ)
    (hf : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt f (p η) (Icc 0 S) η)
    (hp : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt p (q η) (Icc 0 S) η)
    (hq : ∀ η ∈ Icc (0 : ℝ) S, HasDerivWithinAt q (-(5 * f η * q η) - 1 + p η ^ 2) (Icc 0 S) η)
    (hf0 : f 0 = 0) (hp0 : p 0 = 0) (hq0 : q 0 = 1.5355261735) :
    ∃ η ∈ Ioc (0 : ℝ) 4, 1 < p η ∧ ∀ s ∈ Icc 0 η, 0 < q s := by
  have hsub : Icc (0 : ℝ) 4 ⊆ Icc 0 S := Icc_subset_Icc le_rfl hS
  obtain ⟨hp', hq'⟩ := Checked.FSFifth.F5OData.chain (g := f) (p := p) (q := q)
    (fun t ht => (hf t (hsub ht)).mono hsub) (fun t ht => (hp t (hsub ht)).mono hsub)
    (fun t ht => (hq t (hsub ht)).mono hsub) hf0 hp0 hq0
  exact ⟨4, ⟨by norm_num, le_rfl⟩, hp', hq'⟩

/-- Falkner–Skan β = 1/5 in scaled form (coefficient 5), existence: there is a solution of
f''' + 5 f f'' + 1 − f'² = 0 on [0, ∞) (f has derivative p, p has derivative q, q has derivative
−5 f q − 1 + p², one-sided at 0) with f(0) = 0, p(0) = 0 and p(η) → 1 as η → ∞ whose wall value
q(0) = f''(0) lies strictly between 1.5355261734 and 1.5355261735. -/
theorem k5_exists : ∃ f p q : ℝ → ℝ,
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt f (p η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt p (q η) (Ici 0) η) ∧
    (∀ η ∈ Ici (0 : ℝ), HasDerivWithinAt q (-(5 * f η * q η) - 1 + p η ^ 2) (Ici 0) η) ∧
    f 0 = 0 ∧ p 0 = 0 ∧ Tendsto p atTop (𝓝 1) ∧
    1.5355261734 < q 0 ∧ q 0 < 1.5355261735 :=
  Checked.FSFifth.F5ExAssemble.exists_bvp

end Checked.FSFifth
